import ParametricFamilyAudit
import PolynomialCertificateAudit

namespace IndependentParameterAudit
open ConcreteLocalGeometry ParametricLocalGeometry

-- A single closed theorem with all mathematical hypotheses displayed.
theorem actual_family_result : ∀ s : ℂ, s ≠ 0 → s ≠ -(1 / 2 : ℂ) →
    translatedLocalCritical s = localTarget ∧
    translatedLocalCritical s = localAxisIdeal 1 ⊓
      (localAxisIdeal 2 ⊓ localAxisIdeal 3) ∧
    (translatedLocalCritical s).IsRadical ∧
    (localAxisIdeal 1).IsPrime ∧ (localAxisIdeal 2).IsPrime ∧
    (localAxisIdeal 3).IsPrime := by
  intro s hs he
  exact ⟨translatedLocalCritical_eq_localTarget s hs he,
    translatedLocalCritical_eq_axes_intersection s hs he,
    translatedLocalCritical_isRadical s hs he,
    localAxisIdeal_isPrime 1, localAxisIdeal_isPrime 2, localAxisIdeal_isPrime 3⟩

-- The three actual components remain proper and pairwise incomparable.
theorem components_proper : localAxisIdeal 1 ≠ ⊤ ∧
    localAxisIdeal 2 ≠ ⊤ ∧ localAxisIdeal 3 ≠ ⊤ :=
  ⟨localAxisIdeal_ne_top 1, localAxisIdeal_ne_top 2, localAxisIdeal_ne_top 3⟩

theorem components_incomparable :
    (¬ localAxisIdeal 1 ≤ localAxisIdeal 2) ∧
    (¬ localAxisIdeal 2 ≤ localAxisIdeal 1) ∧
    (¬ localAxisIdeal 1 ≤ localAxisIdeal 3) ∧
    (¬ localAxisIdeal 3 ≤ localAxisIdeal 1) ∧
    (¬ localAxisIdeal 2 ≤ localAxisIdeal 3) ∧
    (¬ localAxisIdeal 3 ≤ localAxisIdeal 2) :=
  three_localAxisIdeals_incomparable

end IndependentParameterAudit
#print axioms IndependentParameterAudit.actual_family_result
#print axioms IndependentParameterAudit.components_proper
#print axioms IndependentParameterAudit.components_incomparable
#print axioms ParametricLocalGeometry.parametric_entryJet_provenance
#print axioms ConcreteLocalGeometry.jetCoefficient_eq_coeff
#print axioms ParametricLocalGeometry.translatedEquation_mem_target
#print axioms PolynomialFamilyCertificate.scaledInverse_mul_selected
set_option pp.all true in
#check @IndependentParameterAudit.actual_family_result
