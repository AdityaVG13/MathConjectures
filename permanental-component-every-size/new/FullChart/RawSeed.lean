import FullChart.RawEquivalence
import FullChart.SeedEvaluation
namespace UniformFullChart
noncomputable section
open UniformFullChartSource

theorem seed_finalAmbientDenominator (k : ℕ) :
    ambientSeed k (finalAmbientDenominator k) =
      coefficientSeed k (sourceDenominator k) := by
  change ambientSeed k (backward k (MvPolynomial.C (sourceDenominator k))) = _
  rw [backward_C]
  rfl

theorem seed_ambientNumerator (k : ℕ) :
    seedQuotient k (ambientNumerator k) = coefficientSeed k (sourceDenominator k) := by
  have h := congrArg (ambientSeed k)
    (IsLocalization.Away.sec_spec (ambientPivot k) (finalAmbientDenominator k))
  simp only [map_mul,map_pow] at h
  have hl (x : AmbientQuot k) :
      ambientSeed k (algebraMap (AmbientQuot k) (Ambient k) x) = seedQuotient k x := by
    simp [ambientSeed]
  rw [hl,hl,seedPivot_eq,one_pow,mul_one,seed_finalAmbientDenominator] at h
  exact h.symm

theorem seed_rawChartDenominator (k : ℕ) :
    seedQuotient k (rawChartDenominator k) = coefficientSeed k (sourceDenominator k) := by
  rw [rawChartDenominator,map_mul,seedPivot_eq,one_mul,seed_ambientNumerator]

theorem rawChartDenominator_seed_ne_zero (k : ℕ)
    (h : coefficientSeed k (sourceDenominator k) ≠ 0) :
    seedQuotient k (rawChartDenominator k) ≠ 0 := by
  rw [seed_rawChartDenominator]
  exact h

#print axioms seed_rawChartDenominator
end
end UniformFullChart
