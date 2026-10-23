import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace SparseSeed

open Finset Equiv

/-- The hub is `none`, and the leaves are `some i`. -/
def arrowhead (l : ℕ) : Matrix (Option (Fin l)) (Option (Fin l)) ℂ
  | none, none => -(l : ℂ)
  | none, some _ => 1
  | some _, none => 1
  | some i, some j => if i = j then 1 else 0

private theorem supported_classification (l : ℕ) (σ : Equiv.Perm (Option (Fin l)))
    (h : (∏ i, arrowhead l (σ i) i) ≠ 0) :
    σ = Equiv.swap none (σ none) := by
  have hs (i : Fin l) : σ (some i) = none ∨ σ (some i) = some i := by
    have hn : arrowhead l (σ (some i)) (some i) ≠ 0 := by
      intro hz
      exact h (Finset.prod_eq_zero (Finset.mem_univ _) hz)
    cases he : σ (some i) with
    | none => exact Or.inl rfl
    | some j =>
      right
      have hj : j = i := by
        by_contra hij
        simp [he, arrowhead, hij] at hn
      simp [hj]
  ext x
  cases he : σ none with
  | none =>
    have hid : ∀ i : Fin l, σ (some i) = some i := by
      intro i
      rcases hs i with hi | hi
      · have := σ.injective (hi.trans he.symm)
        cases this
      · exact hi
    cases x with
    | none => simp [he]
    | some i => simp [hid i]
  | some a =>
    have ha : σ (some a) = none := by
      rcases hs a with ha | ha
      · exact ha
      · have := σ.injective (ha.trans he.symm)
        cases this
    have hi (i : Fin l) (hia : i ≠ a) : σ (some i) = some i := by
      rcases hs i with hi | hi
      · have hh := σ.injective (hi.trans ha.symm)
        exact (hia (Option.some.inj hh)).elim
      · exact hi
    cases x with
    | none => simp [he]
    | some i =>
      by_cases hia : i = a
      · subst i; simp [ha]
      · simp [hi i hia, Equiv.swap_apply_of_ne_of_ne, hia]

private theorem swap_weight (l : ℕ) (a : Option (Fin l)) :
    (∏ i, arrowhead l (Equiv.swap none a i) i) =
      match a with | none => -(l : ℂ) | some _ => 1 := by
  rw [Fintype.prod_option]
  cases a with
  | none => simp [arrowhead]
  | some a =>
    have hleaf (i : Fin l) : arrowhead l (Equiv.swap none (some a) (some i)) (some i) = 1 := by
      by_cases hi : i = a
      · subst i; simp [arrowhead]
      · simp [Equiv.swap_apply_of_ne_of_ne, hi, arrowhead]
    simp only [hleaf]
    simp [arrowhead]

private theorem swap_injective (l : ℕ) :
    Function.Injective (fun a : Option (Fin l) => Equiv.swap none a) := by
  intro a b h
  have := congrArg (fun σ : Equiv.Perm (Option (Fin l)) => σ none) h
  simpa using this

/-- A sparse sum can be restricted to the identity and hub/leaf transpositions. -/
private theorem sum_supported (l : ℕ) (f : Equiv.Perm (Option (Fin l)) → ℂ)
    (h : ∀ σ, (∏ i, arrowhead l (σ i) i) = 0 → f σ = 0) :
    (∑ σ, f σ) = ∑ a : Option (Fin l), f (Equiv.swap none a) := by
  rw [← Finset.sum_image (fun a _ b _ hab => swap_injective l hab)]
  apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro σ _ hσ
  apply h
  by_contra hn
  apply hσ
  exact Finset.mem_image.mpr ⟨σ none, Finset.mem_univ _, (supported_classification l σ hn).symm⟩

/-- The uniform sparse seed has zero permanent in every size, including the empty leaf set. -/
theorem permanent_arrowhead (l : ℕ) : (arrowhead l).permanent = 0 := by
  unfold Matrix.permanent
  rw [sum_supported l _ (fun _ h => h)]
  simp_rw [swap_weight]
  rw [Fintype.sum_option]
  simp

/-- The determinant of the uniform sparse seed. -/
theorem det_arrowhead (l : ℕ) : (arrowhead l).det = -2 * (l : ℂ) := by
  rw [Matrix.det_apply]
  rw [sum_supported l _ (fun _ h => by simp [h])]
  simp_rw [swap_weight]
  rw [Fintype.sum_option]
  simp
  ring

/-- In each positive leaf size the sparse seed is invertible. -/
theorem det_arrowhead_ne_zero (l : ℕ) (hl : 1 ≤ l) : (arrowhead l).det ≠ 0 := by
  rw [det_arrowhead]
  exact mul_ne_zero (by norm_num) (by exact_mod_cast (show l ≠ 0 by omega))

/-- The hub/hub permanent cofactor is one. -/
theorem permanent_leaf_submatrix (l : ℕ) :
    ((arrowhead l).submatrix some some).permanent = 1 := by
  have h : (arrowhead l).submatrix some some = (1 : Matrix (Fin l) (Fin l) ℂ) := by
    ext i j
    simp [Matrix.submatrix, arrowhead, Matrix.one_apply]
  rw [h, Matrix.permanent_one]

/-- The explicit witness satisfies the three conditions defining the lower chart. -/
theorem arrowhead_chart_certificate (l : ℕ) (hl : 1 ≤ l) :
    (arrowhead l).permanent = 0 ∧
    ((arrowhead l).submatrix some some).permanent ≠ 0 ∧
    (arrowhead l).det ≠ 0 := by
  exact ⟨permanent_arrowhead l, by rw [permanent_leaf_submatrix]; norm_num,
    det_arrowhead_ne_zero l hl⟩

end SparseSeed

#print axioms SparseSeed.permanent_arrowhead
#print axioms SparseSeed.det_arrowhead
#print axioms SparseSeed.permanent_leaf_submatrix
#print axioms SparseSeed.arrowhead_chart_certificate
