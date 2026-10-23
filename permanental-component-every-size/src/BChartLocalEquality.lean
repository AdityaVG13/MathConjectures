import BChartCoefficientProvenance
import BChartMembership
import BChartRankConsequences
import LocalAssembly
import TargetLocalStructure

/-!
Actual b-chart local ideal equality for every complex s ≠ 0. The polynomial
matrix is the corrected cleared chart, in coordinates T=s+X₀, x3=b, with
error x11 at (2,1). This is the genuine origin localization of P. No ambient
chart/torus equivalence, dimension, or exceptional-parameter claim is made.
-/
namespace BChartLocalGeometry
open ConcreteLocalGeometry

theorem flatEquation_support (s : ℂ) (k : Fin 25) (d : Fin 16 →₀ ℕ)
    (hd : d ∈ (flatEquation s k).support) :
    ∃ i, generatorExponent i ≤ d := by
  have hm : flatEquation s k ∈ targetIdeal :=
    equation_mem_target s (equationPair k).1 (equationPair k).2
  rw [targetIdeal_eq_monomialIdeal] at hm
  exact (LocalGeometryMonomial.mem_monomialIdeal_iff generatorExponent _).mp hm d hd

/-- Rank of the actual generator-coefficient matrix, not the ambient Jacobian. -/
theorem actual_coefficient_rank (s : ℂ) (hs : s ≠ 0) :
    (LocalGeometryMonomial.coefficientMatrix generatorExponent
      (flatEquation s)).rank = 15 := by
  apply le_antisymm (Matrix.rank_le_width _)
  have hr := Matrix.rank_submatrix_le
    (LocalGeometryMonomial.coefficientMatrix generatorExponent (flatEquation s))
    LocalGeometryRank.selectedRows id
  change (LocalGeometryMonomial.coefficientMatrix generatorExponent
    (flatEquation s ∘ LocalGeometryRank.selectedRows)).rank ≤ _ at hr
  rw [actual_selected_coefficient_matrix] at hr
  exact (BChartPolynomialCertificate.selected_rank s
    (BChartPolynomialCertificate.rankScale_ne_zero_complex s hs)).symm.le.trans hr

theorem targetIdeal_generation (s : ℂ) (hs : s ≠ 0) :
    targetIdeal = criticalIdeal s ⊔
      MvPolynomial.idealOfVars (Fin 16) ℂ * targetIdeal := by
  have hinverse : BChartPolynomialCertificate.inverseAt s *
      LocalGeometryMonomial.coefficientMatrix generatorExponent
        (flatEquation s ∘ LocalGeometryRank.selectedRows) = 1 := by
    rw [actual_selected_coefficient_matrix]
    exact BChartPolynomialCertificate.inverseAt_mul_selected s
      (BChartPolynomialCertificate.rankScale_ne_zero_complex s hs)
  have h := LocalGeometryMonomial.monomialIdeal_eq_span_sup_vars_mul_of_selected_leftInverse
    generatorExponent generatorExponent_injective (flatEquation s)
    (flatEquation_support s) LocalGeometryRank.selectedRows
    (BChartPolynomialCertificate.inverseAt s) hinverse
  rw [← targetIdeal_eq_monomialIdeal, flatEquation_range] at h
  exact h

/-- Equality of the actual localized ideals, uniformly for the stated parameter range. -/
theorem localCritical_eq_localTarget (s : ℂ)
    (hs : s ≠ 0) :
    localCritical s = localTarget := by
  have hg := congrArg (Ideal.map (algebraMap P Local)) (targetIdeal_generation s hs)
  rw [Ideal.map_sup, Ideal.map_mul] at hg
  change localTarget = localCritical s ⊔
    Ideal.map (algebraMap P Local) (MvPolynomial.idealOfVars (Fin 16) ℂ) * localTarget at hg
  apply le_antisymm (Ideal.map_mono (criticalIdeal_le_targetIdeal s))
  exact LocalGeometry.ideal_le_of_le_sup_mul_of_le_jacobson
    localTarget_fg map_idealOfVars_le_local_jacobson hg.le

theorem localCritical_eq_axes_intersection (s : ℂ)
    (hs : s ≠ 0) :
    localCritical s = localAxisIdeal 1 ⊓ (localAxisIdeal 2 ⊓ localAxisIdeal 3) := by
  rw [localCritical_eq_localTarget s hs, localTarget_eq_axes_intersection]

theorem localCritical_isRadical (s : ℂ)
    (hs : s ≠ 0) :
    (localCritical s).IsRadical := by
  rw [localCritical_eq_localTarget s hs]
  exact localTarget_isRadical

#print axioms actual_selected_coefficient_matrix
#print axioms actual_coefficient_rank
#print axioms targetIdeal_generation
#print axioms localCritical_eq_localTarget
#print axioms localCritical_eq_axes_intersection
#print axioms localCritical_isRadical
end BChartLocalGeometry
