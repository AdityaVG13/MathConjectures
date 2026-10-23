import RankCertificate
import Mathlib.LinearAlgebra.Matrix.Rank

namespace LocalGeometryRank

/-- The selected 15 by 15 table has full rank over the rationals. -/
theorem selected_rank : selectedMatrix.rank = 15 := by
  apply le_antisymm selectedMatrix.rank_le_width
  have h := Matrix.rank_mul_le_right inverseMatrix selectedMatrix
  simpa only [inverse_mul_selected, Matrix.rank_one, Fintype.card_fin] using h

/-- The complete imported 25 by 15 coefficient table has rank exactly 15. -/
theorem coefficient_rank : coefficientMatrix.rank = 15 := by
  apply le_antisymm coefficientMatrix.rank_le_width
  have h := Matrix.rank_submatrix_le coefficientMatrix selectedRows id
  change selectedMatrix.rank ≤ coefficientMatrix.rank at h
  exact selected_rank.symm.le.trans h

end LocalGeometryRank

#print axioms LocalGeometryRank.selected_rank
#print axioms LocalGeometryRank.coefficient_rank
