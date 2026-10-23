import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Vaserstein.Cited
import Vaserstein.LemmaP

/-!
# Minimum rank of a matrix without a J1 block

`three_le_minRank`: over `F₂`, in dimension `n ≥ 5`, a matrix with no J1 block has minimum rank
at least `3`, which is what Corollary 6.9 of Knüppel–Nielsen needs.

* `rank_map_eq`: rank is unchanged by a field homomorphism, by the rank normal form.
* `finrank_ker_le_frobenius`: for `A` with entries in `F₂`, squaring the coordinates maps the
  `λ`-eigenspace of `A` over the algebraic closure injectively and semilinearly into the
  `λ²`-eigenspace.
-/

namespace Vaserstein

open Matrix Module

section J1

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- If `α - 1` has rank at most `2` and `dim V ≥ 5`, then `α` has a J1 block: the fixed space
has dimension at least `3`, so it is not contained in the image of `α - 1`. -/
theorem hasJ1_of_finrank_range_le {α : GLV (ZMod 2) V} (hn : 5 ≤ finrank (ZMod 2) V)
    (h : finrank (ZMod 2) (LinearMap.range ((α : V →ₗ[ZMod 2] V) - 1)) ≤ 2) : HasJ1 α := by
  set T := (α : V →ₗ[ZMod 2] V) - 1
  have hrk := LinearMap.finrank_range_add_finrank_ker T
  have hnle : ¬ LinearMap.ker T ≤ LinearMap.range T := fun hle =>
    absurd (Submodule.finrank_mono hle) (by omega)
  obtain ⟨v, hvK, hvR⟩ := Set.not_subset.1 hnle
  obtain ⟨φ, hφv, hφR⟩ := exists_dual_one hvR
  refine ⟨v, φ, hφv, ?_, fun x => ?_⟩
  · have : T v = 0 := hvK
    simpa [T, sub_eq_zero] using this
  · have := hφR (T x) (LinearMap.mem_range_self T x)
    simpa [T, sub_eq_zero] using this

end J1

section RankMap

variable {K L : Type*} [Field K] [Field L] {m : Type*} [Fintype m] [DecidableEq m]

/-- The rank of a matrix does not change under a homomorphism of fields. -/
theorem rank_map_eq (f : K →+* L) (A : Matrix m m K) : (A.map f).rank = A.rank := by
  classical
  obtain ⟨P, Q, e, hP, hQ, h⟩ := exists_rank_normal_form A
  set w : m → K := fun i => Sum.elim (fun _ => (1 : K)) (fun _ => 0) (e i)
  have hd := fromBlocks_diagonal (fun _ : Fin A.rank => (1 : K))
    (fun _ : Fin (Fintype.card m - A.rank) => (0 : K))
  rw [diagonal_one, diagonal_zero] at hd
  have hN : P * A * Q = diagonal w := by
    rw [h, hd, submatrix_diagonal_equiv]
    rfl
  have hPd := (isUnit_iff_isUnit_det P).1 hP
  have hQd := (isUnit_iff_isUnit_det Q).1 hQ
  have hPd' := (isUnit_iff_isUnit_det (f.mapMatrix P)).1 (hP.map f.mapMatrix)
  have hQd' := (isUnit_iff_isUnit_det (f.mapMatrix Q)).1 (hQ.map f.mapMatrix)
  have h1 : A.rank = Fintype.card {i // w i ≠ 0} := by
    rw [← rank_diagonal, ← hN, rank_mul_eq_left_of_isUnit_det Q _ hQd,
      rank_mul_eq_right_of_isUnit_det P _ hPd]
  have h2 : (A.map f).rank = Fintype.card {i // f (w i) ≠ 0} := by
    have : f.mapMatrix P * A.map f * f.mapMatrix Q = diagonal (fun i => f (w i)) := by
      rw [← diagonal_map (map_zero f), ← hN]
      simp
    rw [← rank_diagonal, ← this, rank_mul_eq_left_of_isUnit_det _ _ hQd',
      rank_mul_eq_right_of_isUnit_det _ _ hPd']
  rw [h1, h2]
  simp

end RankMap


section Frobenius

local notation "L" => AlgebraicClosure (ZMod 2)

instance : CharP L 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) L).injective 2

variable {n : ℕ}

theorem mem_ker_sub_scalar {B : Matrix (Fin n) (Fin n) L} {μ : L} {v : Fin n → L} :
    v ∈ LinearMap.ker (B - scalar (Fin n) μ).mulVecLin ↔ B *ᵥ v = μ • v := by
  simp [sub_eq_zero]

theorem frobenius_algebraMap (a : ZMod 2) :
    frobenius L 2 (algebraMap (ZMod 2) L a) = algebraMap (ZMod 2) L a := by
  rw [frobenius_def, ← map_pow, ZMod.pow_card]

/-- Squaring the coordinates sends an eigenvector of `A` for `μ` to one for `μ ^ 2`. -/
theorem mulVec_frobenius {A : Matrix (Fin n) (Fin n) (ZMod 2)} {μ : L} {v : Fin n → L}
    (hv : A.map (algebraMap (ZMod 2) L) *ᵥ v = μ • v) :
    A.map (algebraMap (ZMod 2) L) *ᵥ (frobenius L 2 ∘ v) = frobenius L 2 μ • (frobenius L 2 ∘ v) := by
  funext k
  have := congrArg (frobenius L 2) (congrFun hv k)
  simp only [mulVec, dotProduct, map_sum, map_mul, Pi.smul_apply, smul_eq_mul, Matrix.map_apply,
    frobenius_algebraMap] at this ⊢
  exact this

theorem finrank_ker_le_frobenius (A : Matrix (Fin n) (Fin n) (ZMod 2)) (μ : L) :
    finrank L (LinearMap.ker (A.map (algebraMap (ZMod 2) L) - scalar (Fin n) μ).mulVecLin) ≤
      finrank L (LinearMap.ker
        (A.map (algebraMap (ZMod 2) L) - scalar (Fin n) (frobenius L 2 μ)).mulVecLin) := by
  set B := A.map (algebraMap (ZMod 2) L)
  let j : LinearMap.ker (B - scalar (Fin n) μ).mulVecLin →+
      LinearMap.ker (B - scalar (Fin n) (frobenius L 2 μ)).mulVecLin :=
    { toFun := fun v => ⟨frobenius L 2 ∘ (v : Fin n → L),
        mem_ker_sub_scalar.2 (mulVec_frobenius (mem_ker_sub_scalar.1 v.2))⟩
      map_zero' := Subtype.ext (funext fun _ => map_zero _)
      map_add' := fun x y => Subtype.ext (funext fun k =>
        map_add (frobenius L 2) ((x : Fin n → L) k) ((y : Fin n → L) k)) }
  have hj : Function.Injective j := fun x y hxy => by
    ext k
    have : frobenius L 2 ((x : Fin n → L) k) = frobenius L 2 ((y : Fin n → L) k) :=
      congrArg (fun z => (z.1 : Fin n → L) k) hxy
    exact frobenius_inj L 2 this
  have hrk := rank_le_of_injective_injectiveₛ (frobeniusEquiv L 2).symm j
    (frobeniusEquiv L 2).symm.injective hj (fun r v => by
      ext k
      change frobenius L 2 ((frobeniusEquiv L 2).symm r * (v : Fin n → L) k) =
        r * frobenius L 2 ((v : Fin n → L) k)
      rw [map_mul, ← coe_frobeniusEquiv, RingEquiv.apply_symm_apply])
  exact Cardinal.toNat_le_toNat hrk (Module.rank_lt_aleph0 _ _)

theorem two_mul_finrank_ker_le (A : Matrix (Fin n) (Fin n) (ZMod 2)) {μ : L} (h0 : μ ≠ 0)
    (h1 : μ ≠ 1) :
    2 * finrank L (LinearMap.ker (A.map (algebraMap (ZMod 2) L) - scalar (Fin n) μ).mulVecLin) ≤
      n := by
  set B := A.map (algebraMap (ZMod 2) L)
  set K1 := LinearMap.ker (B - scalar (Fin n) μ).mulVecLin
  set K2 := LinearMap.ker (B - scalar (Fin n) (frobenius L 2 μ)).mulVecLin
  have hle : finrank L K1 ≤ finrank L K2 := finrank_ker_le_frobenius A μ
  have hμ : μ - frobenius L 2 μ ≠ 0 := by
    rw [frobenius_def, show μ - μ ^ 2 = μ * (1 - μ) by ring]
    exact mul_ne_zero h0 (sub_ne_zero.2 (Ne.symm h1))
  have hinf : K1 ⊓ K2 = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    have e1 := mem_ker_sub_scalar.1 (Submodule.mem_inf.1 hv).1
    have e2 := mem_ker_sub_scalar.1 (Submodule.mem_inf.1 hv).2
    have : (μ - frobenius L 2 μ) • v = 0 := by rw [sub_smul, ← e1, ← e2, sub_self]
    exact (smul_eq_zero.1 this).resolve_left hμ
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq K1 K2
  have hsup := Submodule.finrank_le (K1 ⊔ K2)
  rw [hinf, finrank_bot, Module.finrank_fin_fun] at *
  omega

/-- Over `F₂`, a matrix with no J1 block in dimension at least `5` has minimum rank at least
`3`. For `λ ∉ F₂`, the eigenspaces for `λ` and `λ²` are independent and squaring the coordinates
embeds the first in the second, so `rank (A - λ) ≥ n - n / 2`. For `λ = 1` this is
`hasJ1_of_finrank_range_le`, and `λ = 0` gives rank `n`. -/
theorem three_le_minRank (hn : 5 ≤ n) (α : GL (Fin n) (ZMod 2))
    (hJ : ¬ HasJ1 (Matrix.GeneralLinearGroup.toLin α)) :
    3 ≤ minRank (α : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  refine le_ciInf fun μ => ?_
  set A := (α : Matrix (Fin n) (Fin n) (ZMod 2))
  by_cases h0 : μ = 0
  · subst h0
    rw [map_zero, sub_zero, rank_map_eq, rank_unit]
    simp only [Fintype.card_fin]
    omega
  by_cases h1 : μ = 1
  · subst h1
    have : A.map (algebraMap (ZMod 2) L) - scalar (Fin n) 1 =
        (algebraMap (ZMod 2) L).mapMatrix (A - 1) := by
      rw [map_one, map_sub, map_one]
      rfl
    rw [this, RingHom.mapMatrix_apply, rank_map_eq]
    by_contra hlt
    refine hJ (hasJ1_of_finrank_range_le (by simpa using hn) ?_)
    have : ((Matrix.GeneralLinearGroup.toLin α : GLV (ZMod 2) (Fin n → ZMod 2)) :
        (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) - 1 = (A - 1).mulVecLin := by
      refine LinearMap.ext fun v => ?_
      simp [A]
    rw [this]
    exact Nat.le_of_lt_succ (not_le.1 hlt)
  have h2 := two_mul_finrank_ker_le A h0 h1
  have h3 := LinearMap.finrank_range_add_finrank_ker (A.map (algebraMap (ZMod 2) L) - scalar (Fin n) μ).mulVecLin
  rw [Module.finrank_fin_fun] at h3
  change 3 ≤ finrank L (LinearMap.range _)
  omega
end Frobenius
end Vaserstein
