import SparseSeed.Cofactors
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace SparseSeed

/-- The complete permanent-cofactor matrix of the lower seed. -/
def cofactorMatrix (l : ℕ) : Matrix (Option (Fin l)) (Option (Fin l)) ℂ := cofactor l

/-- The cofactor determinant is nonzero at every size. -/
theorem det_cofactorMatrix (l : ℕ) : (cofactorMatrix l).det = (-2 : ℂ) ^ l := by
  let e : Option (Fin l) ≃ Fin l ⊕ Unit :=
    (Equiv.optionEquivSumPUnit.{0, 0} (Fin l)).trans (Equiv.sumCongr (Equiv.refl _) (Equiv.equivPUnit Unit).symm)
  let A : Matrix (Fin l) (Fin l) ℂ := fun i j => if i = j then -1 else 1
  let B : Matrix (Fin l) Unit ℂ := fun _ _ => 1
  let C : Matrix Unit (Fin l) ℂ := fun _ _ => 1
  have he : (cofactorMatrix l).submatrix e.symm e.symm = Matrix.fromBlocks A B C 1 := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [e, cofactorMatrix, Matrix.submatrix, Matrix.fromBlocks, cofactor_formula, A]
      | inr j => simp [e, cofactorMatrix, Matrix.submatrix, Matrix.fromBlocks, cofactor_formula, B]
    | inr i =>
      cases j with
      | inl j => simp [e, cofactorMatrix, Matrix.submatrix, Matrix.fromBlocks, cofactor_formula, C]
      | inr j => simp [e, cofactorMatrix, Matrix.submatrix, Matrix.fromBlocks, cofactor_formula]
  have hschur : A - B * C = Matrix.diagonal (fun _ : Fin l => (-2 : ℂ)) := by
    ext i j
    change (if i = j then (-1 : ℂ) else 1) - (∑ _ : Unit, (1 : ℂ) * 1) =
      if i = j then -2 else 0
    split_ifs <;> norm_num
  rw [← Matrix.det_submatrix_equiv_self e.symm (cofactorMatrix l), he,
    Matrix.det_fromBlocks_one₂₂, hschur, Matrix.det_diagonal]
  simp

theorem det_cofactorMatrix_ne_zero (l : ℕ) : (cofactorMatrix l).det ≠ 0 := by
  rw [det_cofactorMatrix]
  exact pow_ne_zero _ (by norm_num)

theorem isUnit_cofactorMatrix (l : ℕ) : IsUnit (cofactorMatrix l) := by
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (det_cofactorMatrix_ne_zero l))

end SparseSeed

#print axioms SparseSeed.det_cofactorMatrix
#print axioms SparseSeed.isUnit_cofactorMatrix
