import FullChart.FinTarget
import GeometryBridge.PolynomialUpperGeometry
import DimensionClosure.LocalizedComponents

set_option autoImplicit false
namespace UniformFullChartTarget
noncomputable section

instance finChart_smooth (k : ℕ) : Algebra.Smooth ℂ (FinChart k) := by
  letI : Algebra.Smooth (FinPoly k) (FinChart k) :=
    Algebra.Smooth.of_isLocalization_Away (finDenom k)
  exact Algebra.Smooth.comp ℂ (FinPoly k) (FinChart k)

theorem finChart_component_dimension (k : ℕ) (Q : Ideal (FinChart k))
    (hQ : IsMinimalPrime Q) :
    ringKrullDim (FinChart k ⧸ Q) = ((k^2+3*k+8 : ℕ) : WithBot ℕ∞) := by
  obtain ⟨hP,_,he⟩ := ComponentDimensionClosure.localized_minimalPrime_dimension
    ℂ (FinPoly k) (FinChart k) (Submonoid.powers (finDenom k)) Q hQ
  rw [he, UniformUpperPolynomial.polyChart_component_dimension (freeCount k) _ hP]
  congr 1
  dsimp [freeCount]
  ring

#print axioms finChart_component_dimension
end
end UniformFullChartTarget
