import FullChart.SourceLocalizationFinal
import FullChart.LocalizationTransport
namespace UniformFullChart
noncomputable section
open UniformFullChartSource UniformFullChartTarget
/-- The explicit retained coefficient denominator pulled back through actual
ambient coordinate elimination. -/
def finalAmbientDenominator (k : ℕ) : Ambient k :=
  liftedDenominator (eliminationAlgEquiv k) (sourceDenominator k)
abbrev ActualFullChart (k : ℕ) := Localization.Away (finalAmbientDenominator k)

/-- Actual ambient chart quotient, on an explicit further principal open, is
a principal localization of a polynomial ring with m²+m+4 variables over Chart.
All maps are composed from proved coordinate equivalences. -/
def actualFullChartEquiv (k : ℕ) : ActualFullChart k ≃ₐ[ℂ] FinChart k :=
  (ambientCoefficientLocalization k (sourceDenominator k)).trans
    ((MvPolynomial.mapAlgEquiv (Fin k) (sourceOpenEquiv k)).trans (fullFinTargetEquiv k))

#print axioms actualFullChartEquiv
end
end UniformFullChart
