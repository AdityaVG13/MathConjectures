import ParametricLocalEquality
import ParametricDenominator

/-!
Independent expected-type checks for the actual translated coordinate-slice
ideals. The localization is fixed at the origin of the sixteen coordinates.
The statements do not assert that translation preserves its maximal ideal,
that there is a full ambient-chart equivalence, or that the excluded parameters
fail to have another local description. No dimension or regularity is asserted.
-/
namespace ParametricFamilyAudit
open MvPolynomial ConcreteLocalGeometry ParametricLocalGeometry

/-- Exact origin and hence the exact multiplicative set being inverted. -/
theorem origin_expected : origin = RingHom.ker
    (eval₂Hom (RingHom.id ℂ) (fun _ : Fin 16 => (0 : ℂ))) := rfl

theorem denominator_set_expected (p : MvPolynomial (Fin 16) ℂ) :
    p ∈ origin.primeCompl ↔
      eval₂Hom (RingHom.id ℂ) (fun _ : Fin 16 => (0 : ℂ)) p ≠ 0 := Iff.rfl

theorem local_type_expected : Local = Localization origin.primeCompl := rfl

theorem localization_instance_expected :
    IsLocalization origin.primeCompl (Localization origin.primeCompl) := inferInstance

/-- The shift really acts on the original polynomial coordinates. -/
theorem translation_definition_expected (s : ℂ) :
    translation s = eval₂Hom C
      (fun i : Fin 16 => if i = 0 then X 0 + C (s - 2) else X i) := rfl

theorem actual_matrix_expected (s : ℂ) :
    N.map (translation s) = matrixWithParameter (C s + X 0) :=
  translatedN_eq_matrixWithParameter s

/-- No proxy equations occur in the ideal whose extension is compared. -/
theorem translated_ideal_definition_expected (s : ℂ) :
    translatedCriticalIdeal s = Ideal.span
      (Set.range (fun ij : Fin 5 × Fin 5 =>
        ((N.map (translation s)).submatrix ij.1.succAbove ij.2.succAbove).permanent)) := rfl

/-- The target is the same actual fifteen-generator ideal for every parameter. -/
theorem target_definition_expected : targetIdeal = Ideal.span
    (Set.range (fun j : Fin 15 =>
      (![X 4,X 5,X 6,X 7,X 8,X 9,X 10,X 11,X 12,X 13,X 14,X 15,
        X 1 * X 2,X 1 * X 3,X 2 * X 3] j : P))) := rfl

theorem generator_exponents_expected : generatorExponent =
    ![Finsupp.single 4 1,Finsupp.single 5 1,Finsupp.single 6 1,
      Finsupp.single 7 1,Finsupp.single 8 1,Finsupp.single 9 1,
      Finsupp.single 10 1,Finsupp.single 11 1,Finsupp.single 12 1,
      Finsupp.single 13 1,Finsupp.single 14 1,Finsupp.single 15 1,
      Finsupp.single 1 1 + Finsupp.single 2 1,
      Finsupp.single 1 1 + Finsupp.single 3 1,
      Finsupp.single 2 1 + Finsupp.single 3 1] := rfl

/-- Full coefficient provenance, not equality only after a jet quotient. -/
theorem actual_coefficient_expected (s : ℂ) (i j : Fin 15) :
    (((N.map (translation s)).submatrix
      (equationPair (LocalGeometryRank.selectedRows i)).1.succAbove
      (equationPair (LocalGeometryRank.selectedRows i)).2.succAbove).permanent).coeff
        (generatorExponent j) =
      PolynomialFamilyCertificate.coefficientMatrix s (LocalGeometryRank.selectedRows i) j :=
  selected_coefficient_provenance s i j

/-- Rank of the actual 25 by 15 generator-coefficient matrix. Quadratic
    generator columns occur, so this is not a claim about the ambient Jacobian. -/
theorem actual_coefficient_rank_expected (s : ℂ) (hs : s ≠ 0) (he : s ≠ -(1/2 : ℂ)) :
    Matrix.rank ((fun (k : Fin 25) (j : Fin 15) =>
      (((N.map (translation s)).submatrix
        (equationPair k).1.succAbove (equationPair k).2.succAbove).permanent).coeff
          (generatorExponent j)) : Matrix (Fin 25) (Fin 15) ℂ) = 15 :=
  actual_coefficient_rank s hs he

/-- Every supported exponent is covered, with no degree bound or extra premise. -/
theorem full_support_expected (s : ℂ) (k : Fin 25) (d : Fin 16 →₀ ℕ)
    (hd : d ∈ (((N.map (translation s)).submatrix
      (equationPair k).1.succAbove (equationPair k).2.succAbove).permanent).support) :
    ∃ i, generatorExponent i ≤ d :=
  translatedFlatEquation_support s k d hd

/-- Global generation modulo the ideal of all variables, before localization. -/
theorem global_generation_expected (s : ℂ) (hs : s ≠ 0) (he : s ≠ -(1/2 : ℂ)) :
    targetIdeal = Ideal.span
      (Set.range (fun ij : Fin 5 × Fin 5 =>
        ((N.map (translation s)).submatrix ij.1.succAbove ij.2.succAbove).permanent)) ⊔
      MvPolynomial.idealOfVars (Fin 16) ℂ * targetIdeal :=
  targetIdeal_generation s hs he

/-- Equality of actual ideal extensions in the genuine fixed-origin localization. -/
theorem local_equality_expected (s : ℂ) (hs : s ≠ 0) (he : s ≠ -(1/2 : ℂ)) :
    Ideal.map (algebraMap P (Localization origin.primeCompl))
      (Ideal.span (Set.range (fun ij : Fin 5 × Fin 5 =>
        ((N.map (translation s)).submatrix ij.1.succAbove ij.2.succAbove).permanent))) =
      Ideal.map (algebraMap P (Localization origin.primeCompl)) targetIdeal :=
  translatedLocalCritical_eq_localTarget s hs he

/-- These are coordinate-plane ideals retaining x0 and xk. -/
theorem axis_definition_expected (k : Fin 16) : axisIdeal k =
    Ideal.span (MvPolynomial.X '' {i : Fin 16 | i ≠ 0 ∧ i ≠ k}) := rfl

theorem exact_prime_intersection_expected (s : ℂ) (hs : s ≠ 0) (he : s ≠ -(1/2 : ℂ)) :
    Ideal.map (algebraMap P (Localization origin.primeCompl)) (translatedCriticalIdeal s) =
      Ideal.map (algebraMap P (Localization origin.primeCompl)) (axisIdeal 1) ⊓
        (Ideal.map (algebraMap P (Localization origin.primeCompl)) (axisIdeal 2) ⊓
          Ideal.map (algebraMap P (Localization origin.primeCompl)) (axisIdeal 3)) :=
  translatedLocalCritical_eq_axes_intersection s hs he

theorem components_prime_expected (k : Fin 16) :
    (Ideal.map (algebraMap P (Localization origin.primeCompl)) (axisIdeal k)).IsPrime :=
  localAxisIdeal_isPrime k

theorem actual_local_ideal_radical_expected (s : ℂ) (hs : s ≠ 0) (he : s ≠ -(1/2 : ℂ)) :
    (Ideal.map (algebraMap P (Localization origin.primeCompl))
      (translatedCriticalIdeal s)).IsRadical :=
  translatedLocalCritical_isRadical s hs he

/-- This denominator-clearing unit check is separate from ambient chart transport. -/
theorem cleared_denominator_unit_expected (s : ℂ) (he : s ≠ -(1/2 : ℂ)) :
    IsUnit (algebraMap P (Localization origin.primeCompl) (translation s den)) :=
  translated_denominator_unit s he

end ParametricFamilyAudit

set_option pp.all true in
#check @ParametricLocalGeometry.translatedLocalCritical_eq_localTarget
#print axioms ParametricLocalGeometry.actual_selected_coefficient_matrix
#print axioms ParametricLocalGeometry.actual_coefficient_rank
#print axioms ParametricLocalGeometry.targetIdeal_generation
#print axioms ParametricLocalGeometry.translatedLocalCritical_eq_localTarget
#print axioms ParametricLocalGeometry.translatedLocalCritical_eq_axes_intersection
#print axioms ParametricLocalGeometry.translatedLocalCritical_isRadical
#print axioms ParametricFamilyAudit.origin_expected
#print axioms ParametricFamilyAudit.denominator_set_expected
#print axioms ParametricFamilyAudit.local_type_expected
#print axioms ParametricFamilyAudit.localization_instance_expected
#print axioms ParametricFamilyAudit.translation_definition_expected
#print axioms ParametricFamilyAudit.actual_matrix_expected
#print axioms ParametricFamilyAudit.translated_ideal_definition_expected
#print axioms ParametricFamilyAudit.target_definition_expected
#print axioms ParametricFamilyAudit.generator_exponents_expected
#print axioms ParametricFamilyAudit.actual_coefficient_expected
#print axioms ParametricFamilyAudit.actual_coefficient_rank_expected
#print axioms ParametricFamilyAudit.full_support_expected
#print axioms ParametricFamilyAudit.global_generation_expected
#print axioms ParametricFamilyAudit.local_equality_expected
#print axioms ParametricFamilyAudit.axis_definition_expected
#print axioms ParametricFamilyAudit.exact_prime_intersection_expected
#print axioms ParametricFamilyAudit.components_prime_expected
#print axioms ParametricFamilyAudit.actual_local_ideal_radical_expected
#print axioms ParametricFamilyAudit.cleared_denominator_unit_expected
