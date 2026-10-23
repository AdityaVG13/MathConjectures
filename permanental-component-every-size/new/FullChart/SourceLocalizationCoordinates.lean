import FullChart.SourceLocalizationFinal

namespace UniformFullChartSource
noncomputable section
open UniformFullChart ComponentLowerChart
open scoped TensorProduct
open TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

attribute [local irreducible] leftLocalizationEquiv rawDeltaTensorEquiv firstOpenTensorEquiv
  firstOpenRetainedEquiv retainedDeltaTensorEquiv

def rawAlgebraMap (k : ℕ) (x : RawTensor k) : RawDeltaOpen k :=
  Localization.mk x 1

theorem leftLocalizationEquiv_tmul (k : ℕ) (u : UpperRawQuot) (b : ActualQuotient k) :
    leftLocalizationEquiv k ((algebraMap UpperRawQuot UpperRawLocalized u) ⊗ₜ[ℂ] b) =
      rawAlgebraMap k ((u ⊗ₜ[ℂ] b) : RawTensor k) := by
  simp only [leftLocalizationEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.comm_tmul, AlgEquiv.coe_restrictScalars,
    IsLocalization.Away.tensorProductEquivTMulRight_tmul,
    IsLocalization.algEquivOfAlgEquiv_eq, rawAlgebraMap]
  rfl

theorem rawDeltaTensorEquiv_tmul (k : ℕ) (u : UpperRawQuot) (b : ActualQuotient k) :
    rawDeltaTensorEquiv k (rawAlgebraMap k ((u ⊗ₜ[ℂ] b) : RawTensor k)) =
      upperActualQuotEquiv.symm (algebraMap UpperRawQuot UpperRawLocalized u) ⊗ₜ[ℂ] b := by
  have he : (leftLocalizationEquiv k).symm
      (rawAlgebraMap k ((u ⊗ₜ[ℂ] b) : RawTensor k)) =
      (algebraMap UpperRawQuot UpperRawLocalized u) ⊗ₜ[ℂ] b := by
    exact (leftLocalizationEquiv k).symm_apply_eq.mpr (leftLocalizationEquiv_tmul k u b).symm
  unfold rawDeltaTensorEquiv
  change (Algebra.TensorProduct.congr upperActualQuotEquiv.symm AlgEquiv.refl)
    ((leftLocalizationEquiv k).symm _) = _
  rw [he]
  rfl

theorem firstOpenTensorEquiv_map (k : ℕ) (q : BaseQuot k) :
    firstOpenTensorEquiv k (algebraMap (BaseQuot k) (FirstOpen k) q) =
      rawDeltaTensorEquiv k (rawAlgebraMap k
        (retainedActualTensorEquiv k q)) := by
  have he : firstOpenRetainedEquiv k (algebraMap (BaseQuot k) (FirstOpen k) q) =
      algebraMap (BaseQuot k) (RetainedDeltaOpen k) q := by
    simpa only [firstOpenRetainedEquiv, AlgEquiv.coe_restrictScalars] using
     (IsLocalization.algEquiv (Submonoid.powers (basePivot k * retainedDelta k))
      (FirstOpen k) (RetainedDeltaOpen k)).commutes q
  simp only [firstOpenTensorEquiv, AlgEquiv.trans_apply, he,
    retainedDeltaTensorEquiv, IsLocalization.algEquivOfAlgEquiv_eq, rawAlgebraMap]
  rfl

/-- The source chart equivalence respects every retained upper coordinate. -/
theorem firstOpenTensorEquiv_upper (k : ℕ) (ij : ComponentChartJacobian.BIndex) :
    firstOpenTensorEquiv k (algebraMap (Base k) (FirstOpen k) (baseEntry k (Sum.inl ij))) =
      (Ideal.Quotient.mk (UniformUpperGauge.cofactorIdeal UniformUpperGauge.matrix)
        (UniformUpperGauge.matrix ij.1 ij.2)) ⊗ₜ[ℂ] (1 : ActualQuotient k) := by
  change firstOpenTensorEquiv k (algebraMap (Base k) (FirstOpen k)
    (algebraMap (BaseQuot k) (Base k) (Ideal.Quotient.mk (baseIdeal k) (MvPolynomial.X (Sum.inl ij))))) = _
  rw [← IsScalarTower.algebraMap_apply, firstOpenTensorEquiv_map]
  have ht := retainedActualTensorEquiv_upper k (MvPolynomial.X ij)
  simp only [MvPolynomial.rename_X, Algebra.TensorProduct.includeLeft_apply] at ht
  rw [ht, rawDeltaTensorEquiv_tmul, upperActualQuotEquiv_symm_mk]
  rfl

/-- The source chart equivalence respects every retained lower coordinate. -/
theorem firstOpenTensorEquiv_lower (k : ℕ) (ij : ComponentChartJacobian.WIndex k) :
    firstOpenTensorEquiv k (algebraMap (Base k) (FirstOpen k) (baseEntry k (Sum.inr ij))) =
      (1 : UpperActualQuot) ⊗ₜ[ℂ] (Ideal.Quotient.mk (actualIdeal k) (MvPolynomial.X ij)) := by
  change firstOpenTensorEquiv k (algebraMap (Base k) (FirstOpen k)
    (algebraMap (BaseQuot k) (Base k) (Ideal.Quotient.mk (baseIdeal k) (MvPolynomial.X (Sum.inr ij))))) = _
  rw [← IsScalarTower.algebraMap_apply, firstOpenTensorEquiv_map]
  have ht := retainedActualTensorEquiv_lower k (MvPolynomial.X ij)
  simp only [MvPolynomial.rename_X, Algebra.TensorProduct.includeRight_apply] at ht
  rw [ht, rawDeltaTensorEquiv_tmul, map_one, map_one]

end
end UniformFullChartSource
#print axioms UniformFullChartSource.firstOpenTensorEquiv_upper
#print axioms UniformFullChartSource.firstOpenTensorEquiv_lower
