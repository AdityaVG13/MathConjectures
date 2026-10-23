import FullChart.ActualEquivalence
set_option backward.isDefEq.respectTransparency false
namespace UniformFullChart
noncomputable section

def ambientNumerator (k : ℕ) : AmbientQuot k :=
  (IsLocalization.Away.sec (ambientPivot k) (finalAmbientDenominator k)).1
def rawChartDenominator (k : ℕ) : AmbientQuot k := ambientPivot k * ambientNumerator k
abbrev RawActualFullChart (k : ℕ) := Localization.Away (rawChartDenominator k)

instance actualFull_numerator (k : ℕ) :
    IsLocalization.Away (algebraMap (AmbientQuot k) (Ambient k) (ambientNumerator k))
      (ActualFullChart k) :=
  (IsLocalization.Away.iff_of_associated (S := ActualFullChart k)
    (IsLocalization.Away.associated_sec_fst (ambientPivot k) (finalAmbientDenominator k))).mpr
      (inferInstance : IsLocalization.Away (finalAmbientDenominator k) (ActualFullChart k))
instance actualFull_raw (k : ℕ) :
    IsLocalization.Away (rawChartDenominator k) (ActualFullChart k) :=
  IsLocalization.Away.mul' (Ambient k) (ActualFullChart k) (ambientPivot k) (ambientNumerator k)

def rawToActualEquiv (k : ℕ) : RawActualFullChart k ≃ₐ[ℂ] ActualFullChart k :=
  (IsLocalization.algEquiv (Submonoid.powers (rawChartDenominator k))
    (RawActualFullChart k) (ActualFullChart k)).restrictScalars ℂ
def rawActualFullChartEquiv (k : ℕ) :
    RawActualFullChart k ≃ₐ[ℂ] UniformFullChartTarget.FinChart k :=
  (rawToActualEquiv k).trans (actualFullChartEquiv k)

#print axioms rawActualFullChartEquiv
end
end UniformFullChart
