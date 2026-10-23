import PolynomialCertificateData
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PolynomialFamilyCertificate
variable {R : Type*} [CommRing R]
/-- Universal polynomial identity over every commutative ring, not interpolation at samples. -/
theorem scaledInverse_mul_selected (s : R) :
    scaledInverse s * selectedMatrix s = rankScale s • (1 : Matrix (Fin 15) (Fin 15) R) := by
  apply Matrix.ext
  intro i
  change ∀ j : Fin 15,
    (∑ k : Fin 15, scaledInverse s i k * selectedMatrix s k j) =
      rankScale s * (if i = j then 1 else 0)
  fin_cases i
  all_goals simp only [Fin.forall_fin_succ]
  all_goals norm_num [Fin.sum_univ_succ,
    selectedMatrix, coefficientMatrix, scaledInverse, LocalGeometryRank.selectedRows,
    Matrix.submatrix, rankScale]
  all_goals repeat' constructor
  all_goals ring
#print axioms scaledInverse_mul_selected
end PolynomialFamilyCertificate
