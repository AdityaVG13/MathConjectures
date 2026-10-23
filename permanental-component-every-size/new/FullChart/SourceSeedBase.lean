import FullChart.SourceLocalizationFinal
import FullChart.UpperSeedOpen
import LowerChart.ActualSeed
set_option backward.isDefEq.respectTransparency false
namespace UniformFullChartSource
noncomputable section
open UniformFullChart ComponentLowerChart UniformUpperGauge
open MvPolynomial TensorProduct
def firstTensorSeed (k : ℕ) : FirstTensor k →ₐ[ℂ] ℂ :=
  Algebra.TensorProduct.lift seedUpperQuotAlg (actualQuotientSeed k) (fun _ _ => Commute.all _ _)
def firstSeed (k : ℕ) : FirstOpen k →ₐ[ℂ] ℂ :=
  (firstTensorSeed k).comp (firstOpenTensorEquiv k).toAlgHom

theorem secondDenominator_seed_ne_zero (k : ℕ) :
    firstSeed k (secondDenominator k) ≠ 0 := by
  simp only [firstSeed,AlgHom.comp_apply,AlgEquiv.toAlgHom_eq_coe,AlgEquiv.coe_algHom,
    secondDenominator,AlgEquiv.apply_symm_apply]
  simp [tensorFinalDenominator,TensorAwayPair.denominator,firstTensorSeed,
    seedUpperQuotAlg,seed_actualDenom_ne_zero]


#print axioms secondDenominator_seed_ne_zero
end
end UniformFullChartSource
