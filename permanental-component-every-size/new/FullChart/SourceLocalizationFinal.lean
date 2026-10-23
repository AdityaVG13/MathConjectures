import FullChart.SourceLocalization

namespace UniformFullChartSource
noncomputable section
open UniformFullChart ComponentLowerChart
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

abbrev tensorFinalDenominator (k : ℕ) : FirstTensor k :=
  TensorAwayPair.denominator UniformUpperGauge.actualDenom (quotientPivot k)

def secondDenominator (k : ℕ) : FirstOpen k :=
  (firstOpenTensorEquiv k).symm (tensorFinalDenominator k)
abbrev SecondOpen (k : ℕ) := Localization.Away (secondDenominator k)

def secondOpenTensorEquiv (k : ℕ) :
    SecondOpen k ≃ₐ[ℂ] UniformUpperGauge.ActualChart ⊗[ℂ] ActualLowerChart k :=
  (IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers (secondDenominator k))
    (T := Submonoid.powers (tensorFinalDenominator k)) (SecondOpen k) (Localization.Away (tensorFinalDenominator k)) (firstOpenTensorEquiv k)
    (by rw [Submonoid.map_powers]; simp [secondDenominator])).trans
      (TensorAwayPair.equivalence UniformUpperGauge.actualDenom (quotientPivot k))

def sourceCoefficientEquiv (k : ℕ) :
    SecondOpen k ≃ₐ[ℂ] UniformUpperGauge.ChartGaugeLocalized ⊗[ℂ] LowerBase k :=
  (secondOpenTensorEquiv k).trans
    (Algebra.TensorProduct.congr UniformUpperGauge.actualChartEquiv (actualLowerChartEquiv k))

/-- A numerator of the second denominator in the first principal localization. -/
def secondNumerator (k : ℕ) : Base k :=
  (IsLocalization.Away.sec (firstDenominator k) (secondDenominator k)).1

def sourceDenominator (k : ℕ) : Base k := firstDenominator k * secondNumerator k
abbrev SourceOpen (k : ℕ) := Localization.Away (sourceDenominator k)

instance secondOpen_numerator (k : ℕ) :
    IsLocalization.Away (algebraMap (Base k) (FirstOpen k) (secondNumerator k)) (SecondOpen k) :=
  (IsLocalization.Away.iff_of_associated (S := SecondOpen k)
    (IsLocalization.Away.associated_sec_fst (firstDenominator k) (secondDenominator k))).mpr
      (inferInstance : IsLocalization.Away (secondDenominator k) (SecondOpen k))

instance secondOpen_combined (k : ℕ) : IsLocalization.Away (sourceDenominator k) (SecondOpen k) :=
  IsLocalization.Away.mul' (FirstOpen k) (SecondOpen k) (firstDenominator k) (secondNumerator k)

def sourceSecondEquiv (k : ℕ) : SourceOpen k ≃ₐ[ℂ] SecondOpen k :=
  (IsLocalization.algEquiv (Submonoid.powers (sourceDenominator k)) (SourceOpen k) (SecondOpen k)).restrictScalars ℂ

/-- A single actual principal open of the retained coefficient chart is the tensor product
of the certified upper and lower charts. No decomposition hypothesis is assumed. -/
def sourceOpenEquiv (k : ℕ) :
    SourceOpen k ≃ₐ[ℂ] UniformUpperGauge.ChartGaugeLocalized ⊗[ℂ] LowerBase k :=
  (sourceSecondEquiv k).trans (sourceCoefficientEquiv k)

end
end UniformFullChartSource
#print axioms UniformFullChartSource.sourceOpenEquiv
