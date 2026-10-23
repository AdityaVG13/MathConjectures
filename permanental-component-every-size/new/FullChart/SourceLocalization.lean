import FullChart.SourceLocalizationTensor
import FullChart.RetainedUpperLocalization
import LowerChart.ActualEquiv

namespace UniformFullChartSource
noncomputable section
open UniformFullChart ComponentLowerChart
open scoped TensorProduct
open TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

abbrev RawTensor (k : ℕ) := UpperRawQuot ⊗[ℂ] ActualQuotient k
def rawDelta (k : ℕ) : RawTensor k := upperRawDelta ⊗ₜ[ℂ] (1 : ActualQuotient k)
abbrev RawDeltaOpen (k : ℕ) := Localization.Away (rawDelta k)
abbrev FirstTensor (k : ℕ) := UpperActualQuot ⊗[ℂ] ActualQuotient k

def leftLocalizationEquiv (k : ℕ) :
    (UpperRawLocalized ⊗[ℂ] ActualQuotient k) ≃ₐ[ℂ] RawDeltaOpen k :=
  (Algebra.TensorProduct.comm ℂ _ _).trans
    (((IsLocalization.Away.tensorProductEquivTMulRight ℂ (ActualQuotient k)
      upperRawDelta UpperRawLocalized).restrictScalars ℂ).trans
      (IsLocalization.algEquivOfAlgEquiv
        (M := Submonoid.powers ((1 : ActualQuotient k) ⊗ₜ[ℂ] upperRawDelta))
        (T := Submonoid.powers (rawDelta k)) _ _
        (Algebra.TensorProduct.comm ℂ _ _) (by
          rw [Submonoid.map_powers]
          simp [rawDelta])))

def rawDeltaTensorEquiv (k : ℕ) : RawDeltaOpen k ≃ₐ[ℂ] FirstTensor k :=
  (leftLocalizationEquiv k).symm.trans
    (Algebra.TensorProduct.congr upperActualQuotEquiv.symm AlgEquiv.refl)

def retainedDelta (k : ℕ) : BaseQuot k := (retainedActualTensorEquiv k).symm (rawDelta k)
abbrev RetainedDeltaOpen (k : ℕ) := Localization.Away (retainedDelta k)

def retainedDeltaTensorEquiv (k : ℕ) : RetainedDeltaOpen k ≃ₐ[ℂ] FirstTensor k :=
  (IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers (retainedDelta k)) (T := Submonoid.powers (rawDelta k))
    _ _ (retainedActualTensorEquiv k) (by
      rw [Submonoid.map_powers]
      simp [retainedDelta])).trans (rawDeltaTensorEquiv k)

theorem retainedPivot_eq (k : ℕ) :
    basePivot k = (retainedActualTensorEquiv k).symm
      ((Ideal.Quotient.mk upperRawIdeal (MvPolynomial.X (0,3))) ⊗ₜ[ℂ] (1 : ActualQuotient k)) := by
  apply (retainedActualTensorEquiv k).injective
  rw [AlgEquiv.apply_symm_apply]
  simpa only [basePivot, MvPolynomial.rename_X, Algebra.TensorProduct.includeLeft_apply] using
    retainedActualTensorEquiv_upper k (MvPolynomial.X (0,3))

theorem retainedPivot_isUnit (k : ℕ) :
    IsUnit (algebraMap (BaseQuot k) (RetainedDeltaOpen k) (basePivot k)) := by
  obtain ⟨n, hn⟩ := (IsLocalization.Away.algebraMap_isUnit_iff (S := UpperRawLocalized)
    upperRawDelta).mp upperRawB03_isUnit
  apply (IsLocalization.Away.algebraMap_isUnit_iff (S := RetainedDeltaOpen k)
    (retainedDelta k)).mpr
  refine ⟨n, ?_⟩
  have ht := map_dvd
    (Algebra.TensorProduct.includeLeft : UpperRawQuot →ₐ[ℂ] RawTensor k) hn
  have hh := map_dvd (retainedActualTensorEquiv k).symm ht
  simpa only [map_pow, Algebra.TensorProduct.includeLeft_apply, ← retainedPivot_eq, retainedDelta, rawDelta] using hh

def firstDenominator (k : ℕ) : Base k := algebraMap (BaseQuot k) (Base k) (retainedDelta k)
abbrev FirstOpen (k : ℕ) := Localization.Away (firstDenominator k)

instance firstOpen_away (k : ℕ) :
    IsLocalization.Away (algebraMap (BaseQuot k) (Base k) (retainedDelta k)) (FirstOpen k) :=
  inferInstanceAs (IsLocalization.Away (firstDenominator k) (FirstOpen k))

instance firstOpen_combined (k : ℕ) :
    IsLocalization.Away (basePivot k * retainedDelta k) (FirstOpen k) :=
  IsLocalization.Away.mul' (Base k) (FirstOpen k) (basePivot k) (retainedDelta k)

instance retainedDeltaOpen_combined (k : ℕ) :
    IsLocalization.Away (basePivot k * retainedDelta k) (RetainedDeltaOpen k) :=
  IsLocalization.Away.mul_of_isUnit' (basePivot k) (retainedDelta k)
    (retainedPivot_isUnit k)

def firstOpenRetainedEquiv (k : ℕ) : FirstOpen k ≃ₐ[ℂ] RetainedDeltaOpen k :=
  (IsLocalization.algEquiv (Submonoid.powers (basePivot k * retainedDelta k))
    (FirstOpen k) (RetainedDeltaOpen k)).restrictScalars ℂ

def firstOpenTensorEquiv (k : ℕ) : FirstOpen k ≃ₐ[ℂ] FirstTensor k :=
  (firstOpenRetainedEquiv k).trans (retainedDeltaTensorEquiv k)

end
end UniformFullChartSource
#print axioms UniformFullChartSource.firstOpenTensorEquiv
