import RankConsequences
import Mathlib.Basic.Complex.Basic

namespace LocalGeometryRank

noncomputable def coefficientMatrixComplex : Matrix (Fin 25) (Fin 15) ℂ :=
  coefficientMatrix.map (Rat.castHom ℂ)

noncomputable def selectedMatrixComplex : Matrix (Fin 15) (Fin 15) ℂ :=
  selectedMatrix.map (Rat.castHom ℂ)

noncomputable def inverseMatrixComplex : Matrix (Fin 15) (Fin 15) ℂ :=
  inverseMatrix.map (Rat.castHom ℂ)

/-- The exact rational inverse identity transported through the actual map Q → C. -/
theorem inverse_mul_selected_complex :
    inverseMatrixComplex * selectedMatrixComplex = 1 := by
  change inverseMatrix.map (Rat.castHom ℂ) * selectedMatrix.map (Rat.castHom ℂ) = 1
  rw [← Matrix.map_mul, inverse_mul_selected]
  simp

theorem selected_rank_complex : selectedMatrixComplex.rank = 15 := by
  apply le_antisymm selectedMatrixComplex.rank_le_width
  have h := Matrix.rank_mul_le_right inverseMatrixComplex selectedMatrixComplex
  simpa only [inverse_mul_selected_complex, Matrix.rank_one, Fintype.card_fin] using h

/-- Rank of the base-changed numeric table, not its polynomial provenance. -/
theorem coefficient_rank_complex : coefficientMatrixComplex.rank = 15 := by
  apply le_antisymm coefficientMatrixComplex.rank_le_width
  have h := Matrix.rank_submatrix_le coefficientMatrixComplex selectedRows id
  change selectedMatrixComplex.rank ≤ coefficientMatrixComplex.rank at h
  exact selected_rank_complex.symm.le.trans h

end LocalGeometryRank

#print axioms LocalGeometryRank.inverse_mul_selected_complex
#print axioms LocalGeometryRank.selected_rank_complex
#print axioms LocalGeometryRank.coefficient_rank_complex
