import PolynomialRankConsequences
import Mathlib.Algebra.Polynomial.Basic

/-!
Expected-type audit of the literal polynomial-table certificate.
The independent literal comparison with results/039.log and 040.log is recorded
in polynomial-literal-audit.log. These checks do not identify the table with
coefficients of actual translated permanent equations; that is a separate theorem.
-/
namespace PolynomialFamilyCertificateAudit
open PolynomialFamilyCertificate
universe u

/-- The selected-row ordering is explicitly part of the audit expectation. -/
theorem selected_rows_expected :
    LocalGeometryRank.selectedRows =
      (![0,1,2,4,5,6,8,9,10,14,15,16,17,18,21] : Fin 15 → Fin 25) := rfl

/-- No field, characteristic, nonzero-parameter, or sampling premise is allowed. -/
theorem universal_identity_expected {R : Type u} [CommRing R] (s : R) :
    scaledInverse s *
      (coefficientMatrix s).submatrix
        (![0,1,2,4,5,6,8,9,10,14,15,16,17,18,21] : Fin 15 → Fin 25) id =
      (72 * s^2 * (1 + 2*s)^3) • (1 : Matrix (Fin 15) (Fin 15) R) :=
  scaledInverse_mul_selected s

/-- This is also an identity in the actual integer polynomial ring at X,
    not merely an identity at numerical parameter values. -/
theorem integer_polynomial_identity_expected :
    scaledInverse (Polynomial.X : Polynomial ℤ) *
      (coefficientMatrix (Polynomial.X : Polynomial ℤ)).submatrix
        (![0,1,2,4,5,6,8,9,10,14,15,16,17,18,21] : Fin 15 → Fin 25) id =
      ((72 : Polynomial ℤ) * (Polynomial.X : Polynomial ℤ)^2 *
        (1 + 2*(Polynomial.X : Polynomial ℤ))^3) •
        (1 : Matrix (Fin 15) (Fin 15) (Polynomial ℤ)) :=
  scaledInverse_mul_selected (Polynomial.X : Polynomial ℤ)

/-- Exact normalized left-inverse orientation over the complex numbers. -/
theorem complex_inverse_expected (s : ℂ) (hs : s ≠ 0) (he : s ≠ -(1/2 : ℂ)) :
    ((72 * s^2 * (1 + 2*s)^3)⁻¹ • scaledInverse s) *
      (coefficientMatrix s).submatrix
        (![0,1,2,4,5,6,8,9,10,14,15,16,17,18,21] : Fin 15 → Fin 25) id =
        (1 : Matrix (Fin 15) (Fin 15) ℂ) :=
  inverseAt_mul_selected s (rankScale_ne_zero_complex s hs he)

/-- Exact rank of the selected square table, with only these two exclusions. -/
theorem complex_selected_rank_expected (s : ℂ) (hs : s ≠ 0) (he : s ≠ -(1/2 : ℂ)) :
    ((coefficientMatrix s).submatrix
      (![0,1,2,4,5,6,8,9,10,14,15,16,17,18,21] : Fin 15 → Fin 25) id).rank = 15 :=
  selected_rank s (rankScale_ne_zero_complex s hs he)

/-- Exact rank of the full 25 by 15 table, not of an unspecified matrix. -/
theorem complex_coefficient_rank_expected (s : ℂ) (hs : s ≠ 0) (he : s ≠ -(1/2 : ℂ)) :
    (coefficientMatrix s).rank = 15 :=
  coefficient_rank_complex s hs he

end PolynomialFamilyCertificateAudit

set_option pp.all true in
#check @PolynomialFamilyCertificate.scaledInverse_mul_selected
#print axioms PolynomialFamilyCertificate.scaledInverse_mul_selected
#print axioms PolynomialFamilyCertificate.inverseAt_mul_selected
#print axioms PolynomialFamilyCertificate.selected_rank
#print axioms PolynomialFamilyCertificate.coefficient_rank_complex
#print axioms PolynomialFamilyCertificateAudit.selected_rows_expected
#print axioms PolynomialFamilyCertificateAudit.universal_identity_expected
#print axioms PolynomialFamilyCertificateAudit.integer_polynomial_identity_expected
#print axioms PolynomialFamilyCertificateAudit.complex_inverse_expected
#print axioms PolynomialFamilyCertificateAudit.complex_selected_rank_expected
#print axioms PolynomialFamilyCertificateAudit.complex_coefficient_rank_expected
