import BChartRankConsequences
import Mathlib.Algebra.Polynomial.Basic

/-! Expected-type checks, separate from the certificate-producing proof.
No geometry over general commutative rings is asserted by this audit. -/
namespace BChartCertificateAudit
open BChartPolynomialCertificate

/-- Exact row order, not merely a cardinality check. -/
theorem selected_rows_exact : LocalGeometryRank.selectedRows =
    ![0, 1, 2, 4, 5, 6, 8, 9, 10, 14, 15, 16, 17, 18, 21] := rfl

/-- C is a left scaled inverse, with scalar exactly 72 s^5. -/
theorem universal_certificate {R : Type*} [CommRing R] (s : R) :
    scaledInverse s * (coefficientMatrix s).submatrix LocalGeometryRank.selectedRows id =
      (72 * s ^ 5) • (1 : Matrix (Fin 15) (Fin 15) R) :=
  scaledInverse_mul_selected s

/-- An actual identity in matrices over Z[X], not sample evaluations. -/
theorem integer_polynomial_certificate :
    scaledInverse (Polynomial.X : Polynomial ℤ) *
      selectedMatrix (Polynomial.X : Polynomial ℤ) =
      (72 * (Polynomial.X : Polynomial ℤ) ^ 5) •
        (1 : Matrix (Fin 15) (Fin 15) (Polynomial ℤ)) :=
  scaledInverse_mul_selected (Polynomial.X : Polynomial ℤ)

/-- The normalized complex inverse has precisely the hypothesis s != 0. -/
theorem complex_left_inverse (s : ℂ) (hs : s ≠ 0) :
    ((72 * s ^ 5)⁻¹ • scaledInverse s) * selectedMatrix s = 1 :=
  inverseAt_mul_selected s (rankScale_ne_zero_complex s hs)

theorem complex_selected_rank (s : ℂ) (hs : s ≠ 0) :
    (selectedMatrix s).rank = 15 :=
  selected_rank s (rankScale_ne_zero_complex s hs)

theorem complex_full_rank (s : ℂ) (hs : s ≠ 0) :
    (coefficientMatrix s).rank = 15 := coefficient_rank_complex s hs

/-- The singularity of A(1)'s determinant does not exclude s=1. -/
theorem parameter_one_rank : (coefficientMatrix (1 : ℂ)).rank = 15 :=
  coefficient_rank_complex 1 one_ne_zero

#print axioms selected_rows_exact
#print axioms universal_certificate
#print axioms integer_polynomial_certificate
#print axioms complex_left_inverse
#print axioms complex_selected_rank
#print axioms complex_full_rank
#print axioms parameter_one_rank
#print axioms BChartPolynomialCertificate.scaledInverse_mul_selected
#print axioms BChartPolynomialCertificate.inverseAt_mul_selected
#print axioms BChartPolynomialCertificate.selected_rank
#print axioms BChartPolynomialCertificate.coefficient_rank_complex
end BChartCertificateAudit
