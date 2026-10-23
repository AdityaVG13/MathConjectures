import SparseSeed.ConstantRows
import Mathlib.Logic.Equiv.Option

set_option autoImplicit false
namespace ComponentGeneralLaplace
open Matrix Equiv

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {R : Type*} [CommSemiring R]

theorem permanent_reindex (e : α ≃ β) (A : Matrix β β R) :
    (A.submatrix e e).permanent = A.permanent := by
  rw [Matrix.permanent, Matrix.permanent]
  apply Fintype.sum_equiv (Equiv.permCongr e)
  intro σ
  apply Fintype.prod_equiv e
  intro i
  simp [Matrix.submatrix]

theorem permanent_option_hub_column {ι : Type*} [DecidableEq ι] [Fintype ι]
    (A : Matrix (Option ι) (Option ι) R) :
    A.permanent = ∑ a : Option ι, A a none *
      (A.submatrix (fun i => Equiv.swap none a (some i)) some).permanent := by
  rw [Matrix.permanent, Finset.univ_perm_option, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  simp [Matrix.permanent, Fintype.prod_option, Finset.mul_sum,
    Matrix.submatrix, Equiv.Perm.decomposeOption, Equiv.Perm.mul_apply]

/-- Arbitrary finite-index column expansion. Both minor axes are indexed by the
complement of j; swapping j with i deletes precisely row i. -/
theorem expand_column (A : Matrix α α R) (j : α) :
    A.permanent = ∑ i : α, A i j *
      (A.submatrix (fun x : {x : α // x ≠ j} => Equiv.swap j i x.val)
        (fun x : {x : α // x ≠ j} => x.val)).permanent := by
  let e := Equiv.optionSubtypeNe j
  rw [← permanent_reindex e A, permanent_option_hub_column]
  apply Fintype.sum_equiv e
  intro i
  simp only [Matrix.submatrix_apply, e, Equiv.optionSubtypeNe_none]
  congr 1
  congr 1
  ext x y
  simp only [Matrix.submatrix_apply]
  rw [e.injective.map_swap]
  rfl

theorem expand_row (A : Matrix α α R) (r : α) :
    A.permanent = ∑ j : α, A r j *
      (A.submatrix (fun x : {x : α // x ≠ r} => x.val)
        (fun x : {x : α // x ≠ r} => Equiv.swap r j x.val)).permanent := by
  rw [← Matrix.permanent_transpose A, expand_column A.transpose r]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Matrix.permanent_transpose]
  rfl

theorem zero_of_row_minors (A : Matrix α α R) (r : α)
    (h : ∀ j, A r j ≠ 0 →
      (A.submatrix (fun x : {x : α // x ≠ r} => x.val)
        (fun x : {x : α // x ≠ r} => Equiv.swap r j x.val)).permanent = 0) :
    A.permanent = 0 := by
  rw [expand_row A r]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : A r j = 0
  · rw [hj, zero_mul]
  · rw [h j hj, mul_zero]

theorem permanent_reindex_independent (er ec : β ≃ α) (A : Matrix α α R) :
    (A.submatrix er ec).permanent = A.permanent := by
  have he : A.submatrix er ec =
      (A.submatrix er er).submatrix id (ec.trans er.symm) := by
    ext i j
    simp [Matrix.submatrix]
  rw [he, Matrix.permanent_permute_rows, permanent_reindex]

def swapComplement (r c : α) : {x : α // x ≠ r} ≃ {x : α // x ≠ c} :=
  (Equiv.swap r c).subtypeEquiv (by
    intro x
    simpa only [Equiv.swap_apply_left] using
      ((Equiv.swap r c).injective.ne_iff (x := x) (y := r)).symm)

theorem zero_of_row_minors_equiv (A : Matrix α α R) (r : α)
    (h : ∀ c, A r c ≠ 0 →
      ∃ (er : β ≃ {x : α // x ≠ r}) (ec : β ≃ {x : α // x ≠ c}),
        (A.submatrix (fun i => (er i).val) (fun j => (ec j).val)).permanent = 0) :
    A.permanent = 0 := by
  apply zero_of_row_minors A r
  intro c hc
  obtain ⟨er,ec,he⟩ := h c hc
  let N := A.submatrix (fun x : {x : α // x ≠ r} => x.val)
    (fun x : {x : α // x ≠ r} => Equiv.swap r c x.val)
  change N.permanent = 0
  rw [← permanent_reindex_independent er (ec.trans (swapComplement r c).symm) N]
  convert he using 1
  congr 1
  ext i j
  simp [N, Matrix.submatrix, swapComplement]

#print axioms zero_of_row_minors_equiv
#print axioms expand_row
#print axioms zero_of_row_minors
#print axioms permanent_reindex
#print axioms expand_column
end ComponentGeneralLaplace
