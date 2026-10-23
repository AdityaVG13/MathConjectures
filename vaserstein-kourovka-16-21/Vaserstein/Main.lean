import Vaserstein.Small
import Vaserstein.Cyclic

/-!
# The main theorem

`covers`: assuming the two cited results, for every `n ≥ 3` every nonidentity element of
`GL(W)`, `dim W = n` over `F₂`, is a product of `k` conjugates of any given nonidentity element,
for every `k ≥ n`. The proof is by strong induction on `n`.

* `n = 3, 4`: the certificates (`covers_three`, `covers_four`).
* `n ≥ 5`, `α` with a J1 block: Case C (`caseC_ge`), which uses dimensions `n - 1` and `n - 2`.
* `n ≥ 5`, `α` without a J1 block: the cyclic route (`cyclic_route`), with
  `2 ⌈(n - 1) / 3⌉ + 1 ≤ n` factors.

`question` answers Kourovka Problem 16.21 for `F = F₂`, in the stronger form `QuestionFrom`.
-/

namespace Vaserstein

open Module Pointwise

universe u

theorem HasJ1.of_conjGL {B B' : Type*} [AddCommGroup B] [Module (ZMod 2) B] [AddCommGroup B']
    [Module (ZMod 2) B'] {s : B ≃ₗ[ZMod 2] B'} {b : GLV (ZMod 2) B} (hJ : HasJ1 (conjGL s b)) :
    HasJ1 b := by
  obtain ⟨v, φ, h1, h2, h3⟩ := hJ
  refine ⟨s.symm v, φ ∘ₗ s.toLinearMap, by simpa using h1, ?_, fun x => ?_⟩
  · simpa using congrArg s.symm h2
  · simpa using h3 (s x)

section Transport

variable {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {m : ℕ}

/-- `GL(W) ≅ GL_m(F₂)` for `dim W = m`. -/
noncomputable def toMatrixGL (hW : finrank (ZMod 2) W = m) : GLV (ZMod 2) W ≃* GL (Fin m) (ZMod 2) :=
  (conjGL (LinearEquiv.ofFinrankEq W (Fin m → ZMod 2) (by simp [hW]))).trans
    Matrix.GeneralLinearGroup.toLin.symm

theorem mem_of_matrix (hW : finrank (ZMod 2) W = m) {j : ℕ}
    (h : ∀ α g : GL (Fin m) (ZMod 2), α ≠ 1 → g ≠ 1 → g ∈ conjugatesOf α ^ j)
    {a b : GLV (ZMod 2) W} (ha : a ≠ 1) (hb : b ≠ 1) : b ∈ conjugatesOf a ^ j :=
  (mem_conjugatesOf_pow_iff_of_mulEquiv (toMatrixGL hW)).1
    (h _ _ ((map_ne_one_iff _ (toMatrixGL hW).injective).2 ha)
      ((map_ne_one_iff _ (toMatrixGL hW).injective).2 hb))

end Transport

/-- **Main theorem**, conditional on the two cited results: for every `n ≥ 3`, every
nonidentity element of `GL_n(F₂)` is a product of `k` conjugates of any nonidentity element,
for every `k ≥ n`. -/
theorem covers (hKN : KnuppelNielsen69) (hBN : BungerNielsen12) :
    ∀ n, 3 ≤ n → Covers.{u} n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn W _ _ _ hW a b ha hb k hk
  have hle : ∀ j, (∀ g : GLV (ZMod 2) W, g ≠ 1 → g ∈ conjugatesOf a ^ j) → j ≤ k →
      b ∈ conjugatesOf a ^ k := fun j h hjk => covers_of_le (exists_conj_ne ha) hjk h b hb
  rcases (show n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | h5
  · exact hle 3 (fun g hg => mem_of_matrix hW covers_three ha hg) hk
  · exact hle 4 (fun g hg => mem_of_matrix hW covers_four ha hg) hk
  by_cases hJ : HasJ1 a
  · exact caseC_ge hW h5 (ih (n - 1) (by omega) (by omega)) (ih (n - 2) (by omega) (by omega))
      ha hJ b hb k hk
  refine hle (1 + 2 * ((n + 1) / 3)) (fun g hg => ?_) (by omega)
  have hJ' : ¬ HasJ1 (Matrix.GeneralLinearGroup.toLin (toMatrixGL hW a)) := fun h =>
    hJ (HasJ1.of_conjGL (by simpa [toMatrixGL] using h))
  exact (mem_conjugatesOf_pow_iff_of_mulEquiv (toMatrixGL hW)).1
    (cyclic_route hKN hBN h5 ((map_ne_one_iff _ (toMatrixGL hW).injective).2 ha) hJ'
      ((map_ne_one_iff _ (toMatrixGL hW).injective).2 hg))

/-- **Kourovka Problem 16.21 over `F₂`**, conditional on the two cited results, in the stronger
form: for `n > 2` and non-central `α, β ∈ SL_n(F₂)`, `β` is a product of `k` matrices similar
to `α` for every `k ≥ n`. -/
theorem questionFrom (hKN : KnuppelNielsen69) (hBN : BungerNielsen12) :
    QuestionFrom (ZMod 2) := by
  intro n hn k hk α β hα hβ
  have hne : ∀ x : Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
      x ∉ Subgroup.center _ → slEquiv n x ≠ 1 := fun x hx h => hx (by
    rw [(map_eq_one_iff _ (slEquiv n).injective).1 h]
    exact Subgroup.one_mem _)
  set t := Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := ZMod 2)
  have hmem : slEquiv n β ∈ conjugatesOf (slEquiv n α) ^ k :=
    (mem_conjugatesOf_pow_iff_of_mulEquiv t).1
      (covers.{0} hKN hBN n hn (Fin n → ZMod 2) (by simp) _ _
        ((map_ne_one_iff _ t.injective).2 (hne α hα))
        ((map_ne_one_iff _ t.injective).2 (hne β hβ)) k hk)
  obtain ⟨f, hf⟩ := Set.mem_pow.1 hmem
  refine ⟨fun i => ((f i : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)), fun i => ?_, ?_⟩
  · obtain ⟨P, hP⟩ := isConj_iff.1 (f i).2
    refine ⟨P, ?_⟩
    change ((f i : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = _
    rw [← hP]
    rfl
  · have := congrArg (Units.coeHom (Matrix (Fin n) (Fin n) (ZMod 2))) hf
    rw [map_list_prod, List.map_ofFn] at this
    exact this

/-- **Kourovka Problem 16.21 over `F₂`**, conditional on the two cited results. -/
theorem question (hKN : KnuppelNielsen69) (hBN : BungerNielsen12) : Question (ZMod 2) :=
  question_of_questionFrom (questionFrom hKN hBN)

end Vaserstein
