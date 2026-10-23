import FullChart.SourceSeed
import FullChart.PolynomialDenominator
namespace UniformFullChart
noncomputable section
open ComponentChartJacobian

theorem rawChartDenominator_ne_zero_at_seed (k : ℕ) :
    seedQuotient k (rawChartDenominator k) ≠ 0 := by
  rw [seed_rawChartDenominator]
  exact UniformFullChartSource.sourceDenominator_seed_ne_zero k

theorem polynomialChartDenominator_ne_zero_at_seed (k : ℕ) :
    MvPolynomial.eval (seed k) (polynomialChartDenominator k) ≠ 0 := by
  rw [polynomialChartDenominator_seed]
  exact UniformFullChartSource.sourceDenominator_seed_ne_zero k

def rawChartSeed (k : ℕ) : RawActualFullChart k →+* ℂ :=
  IsLocalization.Away.lift (rawChartDenominator k)
    (isUnit_iff_ne_zero.mpr (rawChartDenominator_ne_zero_at_seed k))
instance rawActualFullChart_nontrivial (k : ℕ) : Nontrivial (RawActualFullChart k) :=
  (rawChartSeed k).domain_nontrivial

/-- Evaluation on the final chart is the original explicit ambient seed on every polynomial. -/
theorem rawChartSeed_coordinates (k : ℕ) (p : P k) :
    rawChartSeed k (algebraMap (AmbientQuot k) (RawActualFullChart k)
      (Ideal.Quotient.mk (ambientIdeal k) p)) = MvPolynomial.eval (seed k) p := by
  simp [rawChartSeed,seedQuotient]

#print axioms polynomialChartDenominator_ne_zero_at_seed
#print axioms rawChartSeed_coordinates
end
end UniformFullChart
