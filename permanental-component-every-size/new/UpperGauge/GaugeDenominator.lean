import UpperGauge.ActualChart
set_option backward.isDefEq.respectTransparency false
namespace UniformUpperGauge
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem normalGaugeDenom_eq : normalGaugeDenom = ∏ i : Fin 6, (X i : NPoly) := by
  change MvPolynomial.map (algebraMap UniformNormalizedUpper.Quot UniformNormalizedUpper.Normalized) splitDelta = _
  simp [splitDelta_eq]

theorem chartGaugeDenom_eq : chartGaugeDenom = ∏ i : Fin 6, (X i : ChartPoly) := by
  simp [chartGaugeDenom,normalGaugeDenom_eq,coefficientEquiv,MvPolynomial.mapAlgEquiv_apply]

#print axioms chartGaugeDenom_eq
end
end UniformUpperGauge
