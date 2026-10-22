import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.GroupTheory.Perm.Fin

/-!
# Expanding a permanent along its first column

Mathlib defines `Matrix.permanent` as a sum over permutations. This file proves the expansion
along column `0`, the permanent counterpart of `Matrix.det_succ_column_zero`:

  `perm A = ∑ i, A i 0 * perm (A with row i and column 0 deleted)`.

Two uses follow. Applied repeatedly by `simp`, the expansion evaluates the permanent of any
explicit small matrix, so no table of permutations is needed. And if every permanent obtained by
deleting one row and one column vanishes, the permanent itself vanishes
(`permanent_eq_zero_of_cofactors`).
-/

namespace PermanentPartition

open Equiv Finset

variable {R : Type*} [CommSemiring R]

/-- Expansion of the permanent along column `0`. -/
theorem permanent_succ_column_zero {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    A.permanent = ∑ i : Fin (n + 1), A i 0 * (A.submatrix i.succAbove Fin.succ).permanent := by
  rw [Matrix.permanent, Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => Fin.cases ?_ (fun i => ?_) i
  · simp only [Matrix.permanent, Finset.mul_sum, Fin.prod_univ_succ,
      Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
      Equiv.swap_self, Equiv.refl_apply, Fin.succAbove_zero, Matrix.submatrix_apply]
  · -- `univ_perm_fin_succ` lists the permutations through `swap 0 i.succ`, while the deleted
    -- matrix is indexed through `i.succ.succAbove`; `cycleRange` converts one into the other.
    rw [← Matrix.permanent_permute_cols (Fin.cycleRange i)]
    simp only [Matrix.permanent, Finset.mul_sum, Fin.prod_univ_succ, Matrix.submatrix_apply, id,
      Fin.succAbove_cycleRange, Equiv.Perm.decomposeFin_symm_apply_zero,
      Equiv.Perm.decomposeFin_symm_apply_succ]

/-- Expansion of the permanent along any column `j`. -/
theorem permanent_expand_column {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (j : Fin (n + 1)) :
    A.permanent = ∑ i : Fin (n + 1), A i j * (A.submatrix i.succAbove j.succAbove).permanent := by
  -- Reordering the columns by `j.cycleRange.symm` moves column `j` to the front and keeps the
  -- other columns in order, which reduces this to the column `0` expansion.
  have hcols : (⇑j.cycleRange.symm) ∘ Fin.succ = j.succAbove :=
    funext fun k => Fin.cycleRange_symm_succ j k
  rw [← Matrix.permanent_permute_rows j.cycleRange.symm A, permanent_succ_column_zero]
  simp only [Matrix.submatrix_apply, id, Fin.cycleRange_symm_zero, Matrix.submatrix_submatrix,
    Function.id_comp, hcols]
/-- If every permanent with one row and one column deleted vanishes, the permanent vanishes. -/
theorem permanent_eq_zero_of_cofactors {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : ∀ i j : Fin (n + 1), (A.submatrix i.succAbove j.succAbove).permanent = 0) :
    A.permanent = 0 := by
  rw [permanent_succ_column_zero]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hi := h i 0
  simp only [Fin.succAbove_zero] at hi
  rw [hi, mul_zero]

end PermanentPartition
