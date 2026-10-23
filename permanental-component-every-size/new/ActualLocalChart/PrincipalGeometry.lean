import ActualLocalChart.PrincipalTransfer
import ActualLocalChart.Smoothness
import FullChart.RawGeometry

set_option backward.isDefEq.respectTransparency false
namespace ComponentActualLocalChart
noncomputable section
open MvPolynomial ComponentChartJacobian

/-- Transfer the checked full chart onto a principal open of the actual cofactor
scheme. The remaining input is the explicit full-chart denominator's seed value. -/
theorem exists_actual_smooth_principal_chart (k : ℕ)
    (hraw : UniformFullChart.seedQuotient k (UniformFullChart.rawChartDenominator k) ≠ 0) :
    ∃ f : ActualQuotient k, quotientSeedEval k f ≠ 0 ∧
      Algebra.Smooth ℂ (Localization.Away f) ∧
      ∀ Q : Ideal (Localization.Away f), IsMinimalPrime Q →
        ringKrullDim (Localization.Away f ⧸ Q) = ((k^2+3*k+8 : ℕ) : WithBot ℕ∞) := by
  obtain ⟨s, hs, heq⟩ := actual_ideal_equality_on_principal_open k
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (UniformFullChart.rawChartDenominator k)
  have hgn : eval (seed k) g ≠ 0 := by
    have hh := congrArg (UniformFullChart.seedQuotient k) hg
    change eval (seed k) g = _ at hh
    exact hh ▸ hraw
  let f : ActualQuotient k := algebraMap (P k) (ActualQuotient k) (s*g)
  have hf : quotientSeedEval k f ≠ 0 := by
    change eval (seed k) (s*g) ≠ 0
    rw [map_mul]
    exact mul_ne_zero hs hgn
  let B := UniformFullChart.RawActualFullChart k
  let t : B := algebraMap (UniformFullChart.AmbientQuot k) B
    (algebraMap (P k) (UniformFullChart.AmbientQuot k) s)
  let T := Localization.Away t
  have e : Localization.Away f ≃ₐ[ℂ] T := by
    have ee := UniformComponentGeometry.quotientAwayIteratedEquiv (K := ℂ)
      (actualGradientIdeal k) (UniformFullChart.ambientIdeal k) s g heq
    change algebraMap (P k) (UniformFullChart.AmbientQuot k) g = _ at hg
    rw [hg] at ee
    exact ee
  haveI : Algebra.Smooth ℂ T := Algebra.Smooth.comp ℂ B T
  refine ⟨f, hf, Algebra.Smooth.of_equiv e.symm, ?_⟩
  apply ComponentDimensionClosure.component_dimensions_of_equiv e.toRingEquiv
  exact ComponentDimensionClosure.component_dimensions_localization
    ℂ B T (Submonoid.powers t) (k^2+3*k+8)
    (UniformFullChart.rawChart_component_dimension k)

#print axioms exists_actual_smooth_principal_chart
end
end ComponentActualLocalChart
