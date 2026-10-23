import FullChart.RetainedUpperDenominator
import UpperGauge.SeedEvaluation
namespace UniformUpperGauge
noncomputable section
theorem seed_actualDenom_ne_zero : seedUpperQuot actualDenom ≠ 0 := by
  rw [UniformFullChart.actualDenom_eq_explicit]
  change seedLocalization (forwardMap (UniformUpperQuadratic.denom (matrix 1 3) (matrix 2 1))) ≠ 0
  change (seedLocalization.comp forwardMap) (UniformUpperQuadratic.denom (matrix 1 3) (matrix 2 1)) ≠ 0
  rw [seed_forwardMap]
  norm_num [UniformUpperQuadratic.denom,UniformUpperQuadratic.alpha,UniformUpperQuadratic.beta,
    UniformUpperQuadratic.gamma,UniformUpperQuadratic.rest,UniformUpperQuadratic.disc,
    UniformUpperQuadratic.normPlus,UniformUpperQuadratic.normMinus,ComponentUpperSeed.B]
  rw [show seedLocalization (4 : A) = (4 : ℂ) from map_ofNat seedLocalization 4]
  norm_num

def seedActualChart : ActualChart →+* ℂ :=
  IsLocalization.Away.lift actualDenom (isUnit_iff_ne_zero.mpr seed_actualDenom_ne_zero)

instance actualChart_nontrivial : Nontrivial ActualChart := seedActualChart.domain_nontrivial

#print axioms seedActualChart
end
end UniformUpperGauge
