import FullChart.RawEquivalence
import FullChart.RawSeed
import FullChart.TargetGeometry
import DimensionClosure.Equivalence

set_option autoImplicit false
namespace UniformFullChart
noncomputable section

instance rawChart_smooth (k : ℕ) : Algebra.Smooth ℂ (RawActualFullChart k) :=
  Algebra.Smooth.of_equiv (rawActualFullChartEquiv k).symm

theorem rawChart_component_dimension (k : ℕ) (Q : Ideal (RawActualFullChart k))
    (hQ : IsMinimalPrime Q) :
    ringKrullDim (RawActualFullChart k ⧸ Q) = ((k^2+3*k+8 : ℕ) : WithBot ℕ∞) :=
  ComponentDimensionClosure.component_dimensions_of_equiv
    (rawActualFullChartEquiv k).toRingEquiv (k^2+3*k+8)
    (UniformFullChartTarget.finChart_component_dimension k) Q hQ

def rawChartSeedOfNonzero (k : ℕ)
    (h : seedQuotient k (rawChartDenominator k) ≠ 0) : RawActualFullChart k →+* ℂ :=
  IsLocalization.Away.lift (rawChartDenominator k) (isUnit_iff_ne_zero.mpr h)

theorem rawChart_nontrivial (k : ℕ)
    (h : seedQuotient k (rawChartDenominator k) ≠ 0) : Nontrivial (RawActualFullChart k) :=
  (rawChartSeedOfNonzero k h).domain_nontrivial

#print axioms rawChart_component_dimension
end
end UniformFullChart
