import UpperGauge.GaugeDenominator
import LowerChart.UniformPivot
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.MvPolynomial
set_option backward.isDefEq.respectTransparency false
namespace UniformFullChartTarget
noncomputable section
open MvPolynomial TensorProduct
open UniformUpperGauge ComponentLowerChart
abbrev UT := ChartGaugeLocalized
abbrev RawTensor (k : ℕ) := UT ⊗[ℂ] LowerParameters k
def tensorDenom (k : ℕ) : RawTensor k := (1 : UT) ⊗ₜ[ℂ] pivotCoefficient k
abbrev TensorLocalized (k : ℕ) := Localization.Away (tensorDenom k)
def tensorLowerEquiv (k : ℕ) : (UT ⊗[ℂ] LowerBase k) ≃ₐ[ℂ] TensorLocalized k :=
  (IsLocalization.Away.tensorProductEquivTMulRight ℂ UT (pivotCoefficient k) (LowerBase k)).restrictScalars ℂ
abbrev PolyUpper (k : ℕ) := MvPolynomial (FreeLower k) UT
def tensorPolyEquiv (k : ℕ) : RawTensor k ≃ₐ[ℂ] PolyUpper k :=
  (MvPolynomial.algebraTensorAlgEquiv ℂ UT).restrictScalars ℂ
def lowerDenom (k : ℕ) : PolyUpper k := tensorPolyEquiv k (tensorDenom k)
abbrev PolyUpperLocalized (k : ℕ) := Localization.Away (lowerDenom k)
def tensorPolyLocalizedEquiv (k : ℕ) : TensorLocalized k ≃ₐ[ℂ] PolyUpperLocalized k :=
  IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers (tensorDenom k)) (T := Submonoid.powers (lowerDenom k))
    _ _ (tensorPolyEquiv k) (by rw [Submonoid.map_powers]; rfl)

abbrev RawPoly (k : ℕ) := MvPolynomial (FreeLower k) ChartPoly
def upperFactor (k : ℕ) : RawPoly k := C chartGaugeDenom
def lowerFactor (k : ℕ) : RawPoly k :=
  MvPolynomial.map (algebraMap ℂ ChartPoly) (pivotCoefficient k)
def combinedFactor (k : ℕ) : RawPoly k := upperFactor k * lowerFactor k

attribute [local instance] MvPolynomial.algebraMvPolynomial

instance polyUpperLocalization (k : ℕ) : IsLocalization.Away (upperFactor k) (PolyUpper k) := by
  simpa only [upperFactor,Submonoid.map_powers] using
    (inferInstance : IsLocalization ((Submonoid.powers chartGaugeDenom).map
      (C : ChartPoly →+* RawPoly k)) (PolyUpper k))

theorem lowerDenom_eq (k : ℕ) :
    lowerDenom k = algebraMap (RawPoly k) (PolyUpper k) (lowerFactor k) := by
  simp only [lowerDenom,tensorPolyEquiv,tensorDenom,AlgEquiv.coe_restrictScalars,
    MvPolynomial.algebraTensorAlgEquiv_tmul,one_smul]
  change map (algebraMap ℂ UT) (pivotCoefficient k) =
    map (algebraMap ChartPoly UT) (map (algebraMap ℂ ChartPoly) (pivotCoefficient k))
  rw [MvPolynomial.map_map,←IsScalarTower.algebraMap_eq]

instance polyUpper_scalarTower (k : ℕ) : IsScalarTower ℂ (RawPoly k) (PolyUpper k) :=
  IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := RawPoly k) (A := PolyUpper k) (by
    apply RingHom.ext
    intro z
    simp [IsScalarTower.algebraMap_apply ℂ UT (PolyUpper k),
      IsScalarTower.algebraMap_apply ℂ ChartPoly UT]
    change C ((algebraMap ChartPoly UT) (algebraMap ℂ ChartPoly z)) =
      MvPolynomial.map (algebraMap ChartPoly UT) (C (algebraMap ℂ ChartPoly z))
    rw [MvPolynomial.map_C])

instance polyUpperLocalized_away (k : ℕ) :
    IsLocalization.Away (algebraMap (RawPoly k) (PolyUpper k) (lowerFactor k)) (PolyUpperLocalized k) := by
  rw [←lowerDenom_eq]
  infer_instance

instance polyUpperLocalized_combined (k : ℕ) :
    IsLocalization.Away (combinedFactor k) (PolyUpperLocalized k) :=
  IsLocalization.Away.mul' (PolyUpper k) (PolyUpperLocalized k) (upperFactor k) (lowerFactor k)

instance polyUpperLocalized_tower (k : ℕ) :
    IsScalarTower ℂ (RawPoly k) (PolyUpperLocalized k) :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := RawPoly k) (A := PolyUpperLocalized k) (fun z => by
    rw [IsScalarTower.algebraMap_apply ℂ (PolyUpper k) (PolyUpperLocalized k),
      IsScalarTower.algebraMap_apply ℂ (RawPoly k) (PolyUpper k),
      IsScalarTower.algebraMap_apply (RawPoly k) (PolyUpper k) (PolyUpperLocalized k)])

abbrev CombinedLocalized (k : ℕ) := Localization.Away (combinedFactor k)
def combineEquiv (k : ℕ) : PolyUpperLocalized k ≃ₐ[ℂ] CombinedLocalized k :=
  (IsLocalization.algEquiv (Submonoid.powers (combinedFactor k)) _ _).restrictScalars ℂ
def upperLowerTargetEquiv (k : ℕ) : (UT ⊗[ℂ] LowerBase k) ≃ₐ[ℂ] CombinedLocalized k :=
  (tensorLowerEquiv k).trans ((tensorPolyLocalizedEquiv k).trans (combineEquiv k))
#print axioms upperLowerTargetEquiv
end
end UniformFullChartTarget
