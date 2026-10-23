import ActualLocalChart.Smoothness
import ActualLocalChart.Determinant
import DimensionClosure.RefineChart

set_option autoImplicit false
namespace ComponentActualLocalChart
noncomputable section
open ComponentChartJacobian

def quotientDeterminant (k : ℕ) : ActualQuotient k :=
  Ideal.Quotient.mk (actualGradientIdeal k) (actualDeterminant k)

theorem quotientDeterminant_seed_ne_zero (k : ℕ) (hk : 1 ≤ k) :
    quotientSeedEval k (quotientDeterminant k) ≠ 0 :=
  determinant_seed_ne_zero k hk

/-- The final assembly step. Its chart hypotheses must be discharged by the
actual principal-open construction, not by a numerical dimension estimate. -/
theorem actual_component_of_chart (k : ℕ) (hk : 1 ≤ k)
    (f : ActualQuotient k) (hf : quotientSeedEval k f ≠ 0)
    [Algebra.Smooth ℂ (Localization.Away f)]
    (hdim : ∀ Q : Ideal (Localization.Away f), IsMinimalPrime Q →
      ringKrullDim (Localization.Away f ⧸ Q) = ((k^2+3*k+8 : ℕ) : WithBot ℕ∞)) :
    ∃ p : Ideal (ActualQuotient k), IsMinimalPrime p ∧
      ringKrullDim (ActualQuotient k ⧸ p) = ((k^2+3*k+8 : ℕ) : WithBot ℕ∞) ∧
      ∃ U : Set (PrimeSpectrum (ActualQuotient k)),
        U = PrimeSpectrum.zeroLocus p ∩
          (PrimeSpectrum.basicOpen (f*quotientDeterminant k) : Set (PrimeSpectrum (ActualQuotient k))) ∧
        U.Nonempty ∧ closure U = PrimeSpectrum.zeroLocus p ∧
        (∀ x ∈ U, x ∈ Algebra.smoothLocus ℂ (ActualQuotient k) ∧
          quotientDeterminant k ∉ x.asIdeal) := by
  letI : Algebra.FinitePresentation ℂ (ActualQuotient k) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ComponentDimensionClosure.component_from_chart_and_seed
    ℂ (ActualQuotient k) f (quotientDeterminant k) (quotientSeedEval k).toRingHom hf
    (quotientDeterminant_seed_ne_zero k hk) (k^2+3*k+8) hdim

#print axioms actual_component_of_chart
end
end ComponentActualLocalChart
