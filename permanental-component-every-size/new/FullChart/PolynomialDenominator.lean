import FullChart.RawSeed
namespace UniformFullChart
noncomputable section
open ComponentChartJacobian
def polynomialChartDenominator (k : ℕ) : P k :=
  Classical.choose (Ideal.Quotient.mk_surjective (rawChartDenominator k))
theorem polynomialChartDenominator_mk (k : ℕ) :
    Ideal.Quotient.mk (ambientIdeal k) (polynomialChartDenominator k) = rawChartDenominator k :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective (rawChartDenominator k))
theorem polynomialChartDenominator_seed (k : ℕ) :
    MvPolynomial.eval (seed k) (polynomialChartDenominator k) =
      coefficientSeed k (UniformFullChartSource.sourceDenominator k) := by
  have h := congrArg (seedQuotient k) (polynomialChartDenominator_mk k)
  change MvPolynomial.eval (seed k) (polynomialChartDenominator k) = seedQuotient k (rawChartDenominator k) at h
  exact h.trans (seed_rawChartDenominator k)
#print axioms polynomialChartDenominator_seed
end
end UniformFullChart
