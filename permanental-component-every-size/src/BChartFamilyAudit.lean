import BChartCertificateAudit
import BChartDenominator
import BChartLocalEquality

/-! Independent expected-type audit of the actual corrected b-chart objects.
Only the stated complex local-ideal claims are checked. This is neither an
ambient chart isomorphism nor a dimension or all-characteristics theorem. -/
namespace BChartFamilyAudit
open ConcreteLocalGeometry

-- Expose the existing proved prime instance under the explicitly unfolded kernel.
-- This is instance transport, not an additional hypothesis or axiom.
local instance : (RingHom.ker evalOrigin).IsPrime := inferInstanceAs origin.IsPrime

/-- Direct comparison with the corrected displayed 25-entry cleared matrix. -/
theorem displayed_matrix_exact (s : ℂ) :
    BChartLocalGeometry.matrixAt s =
    (let T : P := MvPolynomial.C s + x 0
     let Da := 1 - (T + 1) * x 1
     let Dd := 1 + T * x 2
     let e := T * (1 - x 3)
     let D := e * Da * Dd
     let Qn := -x 3 * (1 + 2 * T) * Da * Dd
     let Jn := T * (1 + x 1) * e * Dd
     let Zn := T * (1 + x 2) * e * Da
     !![1, 1, 1, 1, x 1;
        1, x 4, -1 - x 2 + x 5, x 2, x 6;
        D, Qn - D + D * x 11, D * (1 + x 7), D - Qn + D * x 8, D * (x 1 + x 9);
        Jn + D * x 10, D * x 3, Jn + Zn - T * D + D * x 12, D, D;
        T * D, D * x 3 + D * x 13, Zn + D * x 14, D, -D + D * x 15]) := rfl

/-- No quotient/truncation or signed determinant is substituted for permanents. -/
theorem full_equations_exact (s : ℂ) (ij : Fin 5 × Fin 5) :
    BChartLocalGeometry.equation s ij =
      ((BChartLocalGeometry.matrixAt s).submatrix ij.1.succAbove ij.2.succAbove).permanent := rfl

theorem critical_ideal_exact (s : ℂ) :
    BChartLocalGeometry.criticalIdeal s =
      Ideal.span (Set.range fun ij : Fin 5 × Fin 5 =>
        ((BChartLocalGeometry.matrixAt s).submatrix ij.1.succAbove ij.2.succAbove).permanent) := rfl

theorem target_ideal_exact : targetIdeal = Ideal.span (Set.range
    (![x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15,
       x 1 * x 2, x 1 * x 3, x 2 * x 3] : Fin 15 → P)) := rfl

theorem localization_exact :
    Local = Localization.AtPrime (RingHom.ker evalOrigin) := rfl

theorem origin_is_maximal : (RingHom.ker evalOrigin).IsMaximal := origin_maximal

theorem local_critical_exact (s : ℂ) :
    BChartLocalGeometry.localCritical s =
      Ideal.map (algebraMap P (Localization.AtPrime (RingHom.ker evalOrigin)))
        (BChartLocalGeometry.criticalIdeal s) := rfl

theorem denominator_exact (s : ℂ) :
    BChartLocalGeometry.denominatorAt s = BChartLocalGeometry.matrixAt s 2 0 :=
  BChartLocalGeometry.denominator_eq_matrix_entry s

theorem denominator_value_exact (s : ℂ) :
    evalOrigin (BChartLocalGeometry.denominatorAt s) = s :=
  BChartLocalGeometry.denominator_value s

theorem denominator_is_local_unit (s : ℂ) (hs : s ≠ 0) :
    IsUnit (algebraMap P Local (BChartLocalGeometry.denominatorAt s)) :=
  BChartLocalGeometry.denominator_unit s hs

theorem basepoint_is_row_scaled (s : ℂ) :
    (BChartLocalGeometry.matrixAt s).map evalOrigin =
      fun i j => (![1, 1, s, s, s] i) * PrimitiveFamily.A s i j :=
  BChartLocalGeometry.matrixAt_origin s

/-- Full identities for all three axes and all 25 permanent equations. -/
theorem full_axis_identities (s : ℂ) (k : Fin 3) (r c : Fin 5) :
    axisProjection ⟨k.val + 1, by omega⟩ (BChartLocalGeometry.equation s (r, c)) = 0 :=
  BChartLocalGeometry.axes_vanish s k r c

theorem full_polynomial_containment (s : ℂ) :
    BChartLocalGeometry.criticalIdeal s ≤ targetIdeal :=
  BChartLocalGeometry.criticalIdeal_le_targetIdeal s

/-- All 500 symbolic actual-matrix entry jet identifications. -/
theorem actual_entry_jets (s : ℂ) (r c : Fin 5) (k : Fin 20) :
    entryJet k (BChartLocalGeometry.matrixAt s r c) =
      BChartLocalGeometry.bchartEntryJetTable s r c k :=
  BChartLocalGeometry.bchart_entryJet_provenance s r c k

/-- Actual polynomial coefficients of selected actual permanents, not a rank input. -/
theorem actual_selected_coefficients (s : ℂ) (i j : Fin 15) :
    (BChartLocalGeometry.equation s (equationPair (LocalGeometryRank.selectedRows i))).coeff
      (generatorExponent j) = BChartPolynomialCertificate.selectedMatrix s i j :=
  BChartLocalGeometry.selected_coefficient_provenance s i j

/-- This is the 25-by-15 generator coefficient matrix, not the ambient Jacobian. -/
theorem actual_generator_coefficient_rank (s : ℂ) (hs : s ≠ 0) :
    (LocalGeometryMonomial.coefficientMatrix generatorExponent
      (fun k => BChartLocalGeometry.equation s (equationPair k))).rank = 15 :=
  BChartLocalGeometry.actual_coefficient_rank s hs

/-- No assumed support, inverse, membership, or desired equality premise. -/
theorem actual_generation (s : ℂ) (hs : s ≠ 0) :
    targetIdeal = BChartLocalGeometry.criticalIdeal s ⊔
      MvPolynomial.idealOfVars (Fin 16) ℂ * targetIdeal :=
  BChartLocalGeometry.targetIdeal_generation s hs

theorem actual_local_equality (s : ℂ) (hs : s ≠ 0) :
    Ideal.map (algebraMap P (Localization.AtPrime (RingHom.ker evalOrigin)))
      (Ideal.span (Set.range fun ij : Fin 5 × Fin 5 =>
        ((BChartLocalGeometry.matrixAt s).submatrix ij.1.succAbove ij.2.succAbove).permanent)) =
    Ideal.map (algebraMap P (Localization.AtPrime (RingHom.ker evalOrigin)))
      (Ideal.span (Set.range
        (![x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15,
           x 1 * x 2, x 1 * x 3, x 2 * x 3] : Fin 15 → P))) :=
  BChartLocalGeometry.localCritical_eq_localTarget s hs

/-- The unchanged coordinate primes retain exactly X0 and Xk. -/
theorem local_axis_exact (k : Fin 16) :
    localAxisIdeal k = Ideal.map (algebraMap P Local)
      (Ideal.span (MvPolynomial.X '' {i : Fin 16 | i ≠ 0 ∧ i ≠ k})) := rfl

theorem actual_three_prime_intersection (s : ℂ) (hs : s ≠ 0) :
    BChartLocalGeometry.localCritical s =
      localAxisIdeal 1 ⊓ (localAxisIdeal 2 ⊓ localAxisIdeal 3) :=
  BChartLocalGeometry.localCritical_eq_axes_intersection s hs

theorem three_primes_proper :
    (localAxisIdeal 1).IsPrime ∧ (localAxisIdeal 2).IsPrime ∧ (localAxisIdeal 3).IsPrime ∧
    localAxisIdeal 1 ≠ ⊤ ∧ localAxisIdeal 2 ≠ ⊤ ∧ localAxisIdeal 3 ≠ ⊤ :=
  ⟨localAxisIdeal_isPrime 1, localAxisIdeal_isPrime 2, localAxisIdeal_isPrime 3,
   localAxisIdeal_ne_top 1, localAxisIdeal_ne_top 2, localAxisIdeal_ne_top 3⟩

theorem three_primes_incomparable :
    (¬ localAxisIdeal 1 ≤ localAxisIdeal 2) ∧ (¬ localAxisIdeal 2 ≤ localAxisIdeal 1) ∧
    (¬ localAxisIdeal 1 ≤ localAxisIdeal 3) ∧ (¬ localAxisIdeal 3 ≤ localAxisIdeal 1) ∧
    (¬ localAxisIdeal 2 ≤ localAxisIdeal 3) ∧ (¬ localAxisIdeal 3 ≤ localAxisIdeal 2) :=
  three_localAxisIdeals_incomparable

theorem actual_local_radicality (s : ℂ) (hs : s ≠ 0) :
    (BChartLocalGeometry.localCritical s).IsRadical :=
  BChartLocalGeometry.localCritical_isRadical s hs

theorem parameter_one_included :
    BChartLocalGeometry.localCritical (1 : ℂ) = localTarget :=
  BChartLocalGeometry.localCritical_eq_localTarget 1 one_ne_zero

theorem parameter_neg_half_included :
    BChartLocalGeometry.localCritical (-1 / 2 : ℂ) = localTarget :=
  BChartLocalGeometry.localCritical_eq_localTarget (-1 / 2) (by norm_num)

#print axioms displayed_matrix_exact
#print axioms full_equations_exact
#print axioms critical_ideal_exact
#print axioms target_ideal_exact
#print axioms localization_exact
#print axioms origin_is_maximal
#print axioms local_critical_exact
#print axioms denominator_exact
#print axioms denominator_value_exact
#print axioms denominator_is_local_unit
#print axioms basepoint_is_row_scaled
#print axioms full_axis_identities
#print axioms full_polynomial_containment
#print axioms actual_entry_jets
#print axioms actual_selected_coefficients
#print axioms actual_generator_coefficient_rank
#print axioms actual_generation
#print axioms actual_local_equality
#print axioms local_axis_exact
#print axioms actual_three_prime_intersection
#print axioms three_primes_proper
#print axioms three_primes_incomparable
#print axioms actual_local_radicality
#print axioms parameter_one_included
#print axioms parameter_neg_half_included
end BChartFamilyAudit
