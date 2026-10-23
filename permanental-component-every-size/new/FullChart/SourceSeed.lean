import FullChart.SourceLocalizationCoordinates
import FullChart.SourceSeedBase
import FullChart.SourceLocalizationFinal
import FullChart.SeedEvaluation
import FullChart.UpperSeedOpen
import LowerChart.ActualSeed
set_option backward.isDefEq.respectTransparency false
namespace UniformFullChartSource
noncomputable section
open UniformFullChart ComponentLowerChart UniformUpperGauge ComponentChartJacobian
open MvPolynomial TensorProduct
attribute [local irreducible] firstOpenTensorEquiv

theorem firstSeed_base (k : ℕ) :
    (firstSeed k).toRingHom.comp (algebraMap (UniformFullChart.Base k) (FirstOpen k)) =
      coefficientSeed k := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (basePivot k))
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro z
    change firstSeed k (algebraMap ℂ (FirstOpen k) z) =
      coefficientSeedAlg k (algebraMap ℂ (UniformFullChart.Base k) z)
    simp
  · intro ij
    change firstSeed k (algebraMap (UniformFullChart.Base k) (FirstOpen k) (baseEntry k ij)) =
      coefficientSeed k (baseEntry k ij)
    rw [coefficientSeed_entry]
    cases ij with
    | inl ij =>
      simp [firstSeed,firstTensorSeed,firstOpenTensorEquiv_upper,
        seedUpperQuotAlg,seedUpperQuot,seed,retain,bVar]
    | inr ij =>
      simp [firstSeed,firstTensorSeed,firstOpenTensorEquiv_lower,
        actualSeedCoordinates,seed,retain,wVar]

theorem firstDenominator_seed_ne_zero (k : ℕ) :
    coefficientSeed k (firstDenominator k) ≠ 0 := by
  have h := (IsLocalization.Away.algebraMap_isUnit (S := FirstOpen k)
    (firstDenominator k)).map (firstSeed k).toRingHom
  apply isUnit_iff_ne_zero.mp
  simpa only [←RingHom.comp_apply,firstSeed_base] using h

theorem sourceDenominator_seed_ne_zero (k : ℕ) :
    coefficientSeed k (sourceDenominator k) ≠ 0 := by
  have h := congrArg (firstSeed k)
    (IsLocalization.Away.sec_spec (firstDenominator k) (secondDenominator k))
  have he (x : UniformFullChart.Base k) :
      firstSeed k (algebraMap (UniformFullChart.Base k) (FirstOpen k) x) =
        coefficientSeed k x := RingHom.congr_fun (firstSeed_base k) x
  simp only [map_mul,he,map_pow] at h
  have hn : coefficientSeed k (secondNumerator k) ≠ 0 := by
    unfold secondNumerator
    rw [←h]
    exact mul_ne_zero (secondDenominator_seed_ne_zero k)
      (pow_ne_zero _ (firstDenominator_seed_ne_zero k))
  simpa only [sourceDenominator,map_mul] using
    mul_ne_zero (firstDenominator_seed_ne_zero k) hn

#print axioms sourceDenominator_seed_ne_zero
end
end UniformFullChartSource
