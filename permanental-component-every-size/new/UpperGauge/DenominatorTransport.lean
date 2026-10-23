import UpperGauge.LocalizedSplitting
set_option backward.isDefEq.respectTransparency false
namespace UniformUpperGauge
noncomputable section
open MvPolynomial
abbrev QPoly := MvPolynomial (Fin 6) UniformNormalizedUpper.Quot
abbrev NPoly := MvPolynomial (Fin 6) UniformNormalizedUpper.Normalized

theorem polynomialQuotientAlgEquiv_mk (p : P) :
    polynomialQuotientAlgEquiv (Ideal.Quotient.mk rawIdeal p) =
      MvPolynomial.map (Ideal.Quotient.mk UniformNormalizedUpper.ideal) (polynomialEquiv p) := by
  simp [polynomialQuotientAlgEquiv, MvPolynomial.quotientEquivQuotientMvPolynomial,
    MvPolynomial.map_eq_eval₂Hom_C_comp]

theorem splitDelta_eq : splitDelta = ∏ i : Fin 6, (X i : QPoly) := by
  rw [splitDelta,qDelta,polynomialQuotientAlgEquiv_mk]
  simp only [delta,map_prod]
  simp [pivot,polynomialEquiv, MvPolynomial.renameEquiv,indexEquiv,splitIndex,
    Fin.prod_univ_succ,Fintype.prod_sum_type,mul_assoc]

def normalDenom : QPoly := C UniformNormalizedUpper.qDenom
def bothDenom : QPoly := splitDelta * normalDenom
abbrev BothLocalized := Localization.Away bothDenom
def splitNormalDenom : SplitLocalized := algebraMap QPoly SplitLocalized normalDenom
abbrev TwiceLocalized := Localization.Away splitNormalDenom

instance twiceLocalized_self : IsLocalization.Away (algebraMap QPoly SplitLocalized normalDenom) TwiceLocalized :=
  inferInstanceAs (IsLocalization.Away splitNormalDenom TwiceLocalized)

instance twiceLocalized_isLocalization : IsLocalization.Away bothDenom TwiceLocalized :=
  IsLocalization.Away.mul' SplitLocalized TwiceLocalized splitDelta normalDenom

def twiceEquivBoth : TwiceLocalized ≃ₐ[ℂ] BothLocalized :=
  (IsLocalization.algEquiv (Submonoid.powers bothDenom) TwiceLocalized BothLocalized).restrictScalars ℂ

attribute [local instance] MvPolynomial.algebraMvPolynomial

instance normalPolynomial_scalarTower : IsScalarTower ℂ QPoly NPoly :=
  IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := QPoly) (A := NPoly) (by
    apply RingHom.ext
    intro z
    simp [MvPolynomial.algebraMap_def,
      IsScalarTower.algebraMap_apply ℂ UniformNormalizedUpper.Quot QPoly,
      IsScalarTower.algebraMap_apply ℂ UniformNormalizedUpper.Normalized NPoly,
      IsScalarTower.algebraMap_apply ℂ UniformNormalizedUpper.Quot UniformNormalizedUpper.Normalized]
    rfl)

instance normalPolynomial_isLocalization : IsLocalization.Away normalDenom NPoly := by
  simpa only [normalDenom, Submonoid.map_powers] using
    (inferInstance : IsLocalization ((Submonoid.powers UniformNormalizedUpper.qDenom).map
      (C : UniformNormalizedUpper.Quot →+* QPoly)) NPoly)

def normalGaugeDenom : NPoly := algebraMap QPoly NPoly splitDelta
abbrev NormalGaugeLocalized := Localization.Away normalGaugeDenom

instance normalGauge_self : IsLocalization.Away (algebraMap QPoly NPoly splitDelta) NormalGaugeLocalized :=
  inferInstanceAs (IsLocalization.Away normalGaugeDenom NormalGaugeLocalized)

instance normalGauge_tower : IsScalarTower ℂ QPoly NormalGaugeLocalized :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := QPoly) (A := NormalGaugeLocalized) (fun z => by
    rw [IsScalarTower.algebraMap_apply ℂ NPoly NormalGaugeLocalized,
      IsScalarTower.algebraMap_apply ℂ QPoly NPoly,
      IsScalarTower.algebraMap_apply QPoly NPoly NormalGaugeLocalized])

instance normalGauge_isLocalization : IsLocalization.Away bothDenom NormalGaugeLocalized := by
  exact IsLocalization.Away.mul NPoly NormalGaugeLocalized normalDenom splitDelta

def bothEquivNormalGauge : BothLocalized ≃ₐ[ℂ] NormalGaugeLocalized :=
  (IsLocalization.algEquiv (Submonoid.powers bothDenom) BothLocalized NormalGaugeLocalized).restrictScalars ℂ

abbrev ChartPoly := MvPolynomial (Fin 6) UniformUpperQuadratic.Chart
def coefficientEquiv : NPoly ≃ₐ[ℂ] ChartPoly :=
  MvPolynomial.mapAlgEquiv (Fin 6) UniformNormalizedUpper.normalizedAlgEquiv.symm
def chartGaugeDenom : ChartPoly := coefficientEquiv normalGaugeDenom
abbrev ChartGaugeLocalized := Localization.Away chartGaugeDenom

def normalGaugeEquivChart : NormalGaugeLocalized ≃ₐ[ℂ] ChartGaugeLocalized :=
  IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers normalGaugeDenom) (T := Submonoid.powers chartGaugeDenom)
    NormalGaugeLocalized ChartGaugeLocalized coefficientEquiv
    (by rw [Submonoid.map_powers]; rfl)

def splitChartEquiv : TwiceLocalized ≃ₐ[ℂ] ChartGaugeLocalized :=
  twiceEquivBoth.trans (bothEquivNormalGauge.trans normalGaugeEquivChart)
#print axioms splitChartEquiv
end
end UniformUpperGauge
