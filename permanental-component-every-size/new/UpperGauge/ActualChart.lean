import UpperGauge.DenominatorTransport
set_option backward.isDefEq.respectTransparency false
namespace UniformUpperGauge
noncomputable section
def coordinateAlgEquiv : A ≃ₐ[ℂ] A :=
  { coordinateRingEquiv with
    commutes' := by
      intro z
      change forwardMap (algebraMap P A (MvPolynomial.C z)) = algebraMap P A (MvPolynomial.C z)
      simp [forwardMap,forwardPoly] }

def actualQuotientAlgEquiv :
    (A ⧸ cofactorIdeal matrix) ≃ₐ[ℂ] NormalizedPivotQuot :=
  Ideal.quotientEquivAlg _ _ coordinateAlgEquiv.symm map_cofactorIdeal.symm

def actualLaurentEquiv : (A ⧸ cofactorIdeal matrix) ≃ₐ[ℂ] SplitLocalized :=
  actualQuotientAlgEquiv.trans normalizedLaurentEquiv

/-- Pull back the explicit normalized denominator along the actual coordinate equivalence. -/
def actualDenom : A ⧸ cofactorIdeal matrix :=
  actualLaurentEquiv.symm splitNormalDenom
abbrev ActualChart := Localization.Away actualDenom

def actualChartToTwice : ActualChart ≃ₐ[ℂ] TwiceLocalized :=
  IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers actualDenom) (T := Submonoid.powers splitNormalDenom)
    ActualChart TwiceLocalized actualLaurentEquiv
    (by rw [Submonoid.map_powers]; simp [actualDenom])

/-- The actual six-pivot upper permanent chart, with the normalized denominator inverted,
is a principal localization of the polynomial algebra in six gauge parameters over Chart. -/
def actualChartEquiv : ActualChart ≃ₐ[ℂ] ChartGaugeLocalized :=
  actualChartToTwice.trans splitChartEquiv

#print axioms actualChartEquiv
end
end UniformUpperGauge
