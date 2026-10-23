import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Vaserstein.MinRank
import Vaserstein.ClassN
import Vaserstein.CaseC

/-!
# The cyclic route

Let `n ≥ 5` and let `α ∈ GL_n(F₂)`, `α ≠ 1`, have no J1 block, so `δ(α) ≥ 3`
(`three_le_minRank`). Write `C` for the conjugacy class of `α` and `k = ⌈(n - 1) / 3⌉`.

1. Corollary 6.9 of Knüppel–Nielsen, applied to `k` copies of `C`, gives a cyclic
   `D ∈ C^k`. Its inverse is cyclic too (`cyclicMatrix_inv`).
2. Let `r` be monic irreducible of degree `n - 1` (`exists_irreducible`). Theorem 1.2 of
   Bünger–Nielsen gives `α = d' x'` with `x'` similar to `D⁻¹` and `r ∣ minpoly d'`, so
   `d' ∈ C · C^k`. It also gives `g = d x` with `x` similar to `D` and `r ∣ minpoly d`.
3. `d` and `d'` are conjugate (`isConj_of_dvd_minpoly`), so `d ∈ C^(k+1)` and
   `g ∈ C^(2k+1)`.
-/

namespace Vaserstein

open Matrix Module Polynomial Pointwise

variable {n : ℕ}

/-- A monic irreducible polynomial over `F₂` of degree `k ≥ 2` with nonzero constant term: the
minimal polynomial of a primitive element of `GF(2^k)`. -/
theorem exists_irreducible {k : ℕ} (hk : 2 ≤ k) :
    ∃ r : (ZMod 2)[X], r.Monic ∧ Irreducible r ∧ r.natDegree = k ∧ r.coeff 0 ≠ 0 := by
  obtain ⟨ζ, hζ⟩ := Field.exists_primitive_element_of_finite_top (ZMod 2) (GaloisField 2 k)
  have hint : IsIntegral (ZMod 2) ζ := Algebra.IsIntegral.isIntegral ζ
  have hdeg : (minpoly (ZMod 2) ζ).natDegree = k := by
    rw [← IntermediateField.adjoin.finrank hint, hζ, IntermediateField.finrank_top',
      GaloisField.finrank 2 (by omega)]
  refine ⟨minpoly _ ζ, minpoly.monic hint, minpoly.irreducible hint, hdeg,
    minpoly.coeff_zero_ne_zero hint ?_⟩
  rintro rfl
  rw [minpoly.zero, natDegree_X] at hdeg
  omega

/-- The inverse of a cyclic invertible matrix is cyclic: if `v, D v, …, D^(n-1) v` is a basis,
then `D^(n-1) v` is a cyclic vector for `D⁻¹`. -/
theorem cyclicMatrix_inv {K : Type*} [Field K] {D : GL (Fin n) K}
    (h : CyclicMatrix (D : Matrix (Fin n) (Fin n) K)) :
    CyclicMatrix ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨v, hv⟩ := h
  refine ⟨(D : Matrix (Fin n) (Fin n) K) ^ (n - 1) *ᵥ v, ?_⟩
  have key : ∀ i : Fin n,
      ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ (i : ℕ) *ᵥ
        ((D : Matrix (Fin n) (Fin n) K) ^ (n - 1) *ᵥ v) =
      (D : Matrix (Fin n) (Fin n) K) ^ (Fin.rev i : ℕ) *ᵥ v := by
    intro i
    have hg : D⁻¹ ^ (i : ℕ) * D ^ (n - 1) = D ^ (Fin.rev i : ℕ) := by
      rw [Fin.val_rev, show n - 1 = (i : ℕ) + (n - (i + 1)) by omega, pow_add, inv_pow,
        inv_mul_cancel_left]
    rw [mulVec_mulVec, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
      hg, Units.val_pow_eq_pow_val]
  have := hv.comp Fin.rev Fin.rev_injective
  convert this using 1
  funext i
  exact key i

/-- Over `F₂` every invertible matrix has determinant `1`, so `SL_n(F₂) = GL_n(F₂)`. -/
noncomputable def slEquiv (n : ℕ) : SpecialLinearGroup (Fin n) (ZMod 2) ≃* GL (Fin n) (ZMod 2) :=
  MulEquiv.ofBijective SpecialLinearGroup.toGL ⟨SpecialLinearGroup.toGL_injective, fun g =>
    ⟨⟨g, (zmod2_cases _).resolve_left
      ((isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero⟩, Units.ext rfl⟩⟩

@[simp] theorem coe_slEquiv (x : SpecialLinearGroup (Fin n) (ZMod 2)) :
    ((slEquiv n x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = x := rfl

@[simp] theorem coe_slEquiv_symm (g : GL (Fin n) (ZMod 2)) :
    ((((slEquiv n).symm g : SpecialLinearGroup (Fin n) (ZMod 2))) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = g := by
  rw [← coe_slEquiv, MulEquiv.apply_symm_apply]

theorem notMem_center_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {a : G}
    (h : ∃ y : H, y * e a * y⁻¹ ≠ e a) : a ∉ Subgroup.center G := by
  intro ha
  obtain ⟨y, hy⟩ := h
  apply hy
  rw [mul_inv_eq_iff_eq_mul]
  have := Subgroup.mem_center_iff.1 ha (e.symm y)
  calc y * e a = e (e.symm y * a) := by simp
    _ = e (a * e.symm y) := by rw [this]
    _ = e a * y := by simp

/-- A nonidentity element of `GL_n(F₂)` is not central. -/
theorem exists_conj_ne_GL {α : GL (Fin n) (ZMod 2)} (hα : α ≠ 1) : ∃ y, y * α * y⁻¹ ≠ α := by
  set t := Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := ZMod 2)
  obtain ⟨x, hx⟩ := exists_conj_ne (α := t α) (fun h => hα (by simpa using congrArg t.symm h))
  refine ⟨t.symm x, fun h => hx ?_⟩
  have := congrArg t h
  simpa using this

theorem minpoly_toLin (d : GL (Fin n) (ZMod 2)) :
    minpoly (ZMod 2) ((Matrix.GeneralLinearGroup.toLin d : GLV (ZMod 2) (Fin n → ZMod 2)) :
      (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) =
    minpoly (ZMod 2) (d : Matrix (Fin n) (Fin n) (ZMod 2)) :=
  Matrix.minpoly_toLin' _

theorem not_homothety {M : GL (Fin n) (ZMod 2)} (hn : 0 < n) (hM : M ≠ 1) (c : ZMod 2) :
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) ≠ Matrix.scalar (Fin n) c := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rcases zmod2_cases c with rfl | rfl
  · intro h
    have := M.val_inv
    rw [map_zero] at h
    rw [h, zero_mul] at this
    exact zero_ne_one this
  · intro h
    exact hM (Units.ext (by simpa using h))

theorem mem_of_isConj_pow {G : Type*} [Group G] {a b y : G} {k : ℕ}
    (hb : b ∈ conjugatesOf a ^ k) (h : IsConj b y) : y ∈ conjugatesOf a ^ k := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact conj_mem_conjugatesOf_pow c hb

/-- **The cyclic route.** Over `F₂`, with `n ≥ 5`, let `α ≠ 1` have no J1 block. Then every
`g ≠ 1` is a product of `2 ⌈(n - 1) / 3⌉ + 1` conjugates of `α`. -/
theorem cyclic_route (hKN : KnuppelNielsen69) (hBN : BungerNielsen12) (hn : 5 ≤ n)
    {α : GL (Fin n) (ZMod 2)} (hα : α ≠ 1)
    (hJ : ¬ HasJ1 (Matrix.GeneralLinearGroup.toLin α)) {g : GL (Fin n) (ZMod 2)} (hg : g ≠ 1) :
    g ∈ conjugatesOf α ^ (1 + 2 * ((n + 1) / 3)) := by
  set k := (n + 1) / 3
  have hδ := three_le_minRank hn α hJ
  have hαc : (slEquiv n).symm α ∉ Subgroup.center (SpecialLinearGroup (Fin n) (ZMod 2)) :=
    notMem_center_of_mulEquiv (slEquiv n) (by simpa using exists_conj_ne_GL hα)
  obtain ⟨c, hc, hcyc⟩ := hKN n (by omega) (by omega) k (fun _ => (slEquiv n).symm α)
    (fun _ => hαc) (by
    simp only [coe_slEquiv_symm, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    have : n - 1 ≤ k * 3 := by omega
    exact this.trans (Nat.mul_le_mul_left k hδ))
  set D := slEquiv n (List.ofFn c).prod
  have hD : D ∈ conjugatesOf α ^ k := by
    refine Set.mem_pow.2 ⟨fun i => ⟨slEquiv n (c i), ?_⟩, ?_⟩
    · have := (slEquiv n).toMonoidHom.map_isConj (hc i)
      rwa [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at this
    · simp only [D, map_list_prod, List.map_ofFn]
      rfl
  have hDc : CyclicMatrix (D : Matrix (Fin n) (Fin n) (ZMod 2)) := by simpa [D] using hcyc
  obtain ⟨r, hrm, hri, hrd, hr0⟩ := exists_irreducible (k := n - 1) (by omega)
  obtain ⟨d', x', hx', hd', hα'⟩ := hBN n (by omega) α (not_homothety (by omega) hα) D⁻¹
    (cyclicMatrix_inv hDc) r hrm hrd hr0
  obtain ⟨d, x, hx, hd, rfl⟩ := hBN n (by omega) g (not_homothety (by omega) hg) D hDc r hrm hrd
    hr0
  set t := Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := ZMod 2)
  have hconj : IsConj d' d := by
    have h := isConj_of_dvd_minpoly (V := Fin n → ZMod 2) (u := t d') (u' := t d)
      (by simp) (by omega) hrm hri hrd (by rwa [minpoly_toLin]) (by rwa [minpoly_toLin])
    simpa using t.symm.toMonoidHom.map_isConj h
  have hx'i : x'⁻¹ ∈ conjugatesOf α ^ k := by
    refine mem_of_isConj_pow hD ?_
    obtain ⟨q, hq⟩ := isConj_iff.1 hx'
    exact isConj_iff.2 ⟨q, by rw [← hq]; group⟩
  have hdmem : d ∈ conjugatesOf α ^ (1 + k) := by
    obtain ⟨P, rfl⟩ := isConj_iff.1 hconj
    have hd'e : d' = α * x'⁻¹ := eq_mul_inv_of_mul_eq hα'.symm
    have h1 : P * α * P⁻¹ ∈ conjugatesOf α ^ 1 := by
      rw [pow_one]
      exact conj_mem_conjugatesOf P (IsConj.refl α)
    have := mem_pow_add h1 (conj_mem_conjugatesOf_pow P hx'i)
    rw [hd'e]
    convert this using 1
    group
  have := mem_pow_add hdmem (mem_of_isConj_pow hD hx)
  rwa [show 1 + k + k = 1 + 2 * k by ring] at this

end Vaserstein
