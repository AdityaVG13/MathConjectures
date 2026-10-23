import ParametricCoefficientProvenance
import PolynomialRankConsequences
import LocalAssembly
import TargetLocalStructure

/-!
Local equality for the actual translated q-chart equations, at every parameter
s ≠ 0, -1/2. The localization is the original origin-local polynomial ring,
now applied to translated equations; translation is NOT asserted to preserve
that maximal ideal. No ambient chart/torus isomorphism is claimed.
-/
namespace ParametricLocalGeometry
open ConcreteLocalGeometry

noncomputable def translatedLocalCritical (s : ℂ) : Ideal Local :=
  Ideal.map (algebraMap P Local) (translatedCriticalIdeal s)

theorem translatedFlatEquation_support (s : ℂ) (k : Fin 25) (d : Fin 16 →₀ ℕ)
    (hd : d ∈ (translatedFlatEquation s k).support) :
    ∃ i, generatorExponent i ≤ d := by
  have hm : translatedFlatEquation s k ∈ targetIdeal :=
    translatedEquation_mem_target s (equationPair k).1 (equationPair k).2
  rw [targetIdeal_eq_monomialIdeal] at hm
  exact (LocalGeometryMonomial.mem_monomialIdeal_iff generatorExponent _).mp hm d hd

/-- Rank of the actual generator-coefficient matrix, not the ambient Jacobian. -/
theorem actual_coefficient_rank (s : ℂ) (hs : s ≠ 0) (he : s ≠ -(1/2 : ℂ)) :
    (LocalGeometryMonomial.coefficientMatrix generatorExponent
      (translatedFlatEquation s)).rank = 15 := by
  apply le_antisymm (Matrix.rank_le_width _)
  have hr := Matrix.rank_submatrix_le
    (LocalGeometryMonomial.coefficientMatrix generatorExponent (translatedFlatEquation s))
    LocalGeometryRank.selectedRows id
  change (LocalGeometryMonomial.coefficientMatrix generatorExponent
    (translatedFlatEquation s ∘ LocalGeometryRank.selectedRows)).rank ≤ _ at hr
  rw [actual_selected_coefficient_matrix] at hr
  exact (PolynomialFamilyCertificate.selected_rank s
    (PolynomialFamilyCertificate.rankScale_ne_zero_complex s hs he)).symm.le.trans hr

theorem targetIdeal_generation (s : ℂ) (hs : s ≠ 0) (he : s ≠ -(1/2 : ℂ)) :
    targetIdeal = translatedCriticalIdeal s ⊔
      MvPolynomial.idealOfVars (Fin 16) ℂ * targetIdeal := by
  have hinverse : PolynomialFamilyCertificate.inverseAt s *
      LocalGeometryMonomial.coefficientMatrix generatorExponent
        (translatedFlatEquation s ∘ LocalGeometryRank.selectedRows) = 1 := by
    rw [actual_selected_coefficient_matrix]
    exact PolynomialFamilyCertificate.inverseAt_mul_selected s
      (PolynomialFamilyCertificate.rankScale_ne_zero_complex s hs he)
  have h := LocalGeometryMonomial.monomialIdeal_eq_span_sup_vars_mul_of_selected_leftInverse
    generatorExponent generatorExponent_injective (translatedFlatEquation s)
    (translatedFlatEquation_support s) LocalGeometryRank.selectedRows
    (PolynomialFamilyCertificate.inverseAt s) hinverse
  rw [← targetIdeal_eq_monomialIdeal, translatedFlatEquation_range] at h
  exact h

/-- Equality of the actual localized ideals, uniformly for the stated parameter range. -/
theorem translatedLocalCritical_eq_localTarget (s : ℂ)
    (hs : s ≠ 0) (he : s ≠ -(1/2 : ℂ)) :
    translatedLocalCritical s = localTarget := by
  have hg := congrArg (Ideal.map (algebraMap P Local)) (targetIdeal_generation s hs he)
  rw [Ideal.map_sup, Ideal.map_mul] at hg
  change localTarget = translatedLocalCritical s ⊔
    Ideal.map (algebraMap P Local) (MvPolynomial.idealOfVars (Fin 16) ℂ) * localTarget at hg
  apply le_antisymm (Ideal.map_mono (translatedCriticalIdeal_le_targetIdeal s))
  exact LocalGeometry.ideal_le_of_le_sup_mul_of_le_jacobson
    localTarget_fg map_idealOfVars_le_local_jacobson hg.le

theorem translatedLocalCritical_eq_axes_intersection (s : ℂ)
    (hs : s ≠ 0) (he : s ≠ -(1/2 : ℂ)) :
    translatedLocalCritical s = localAxisIdeal 1 ⊓ (localAxisIdeal 2 ⊓ localAxisIdeal 3) := by
  rw [translatedLocalCritical_eq_localTarget s hs he, localTarget_eq_axes_intersection]

theorem translatedLocalCritical_isRadical (s : ℂ)
    (hs : s ≠ 0) (he : s ≠ -(1/2 : ℂ)) :
    (translatedLocalCritical s).IsRadical := by
  rw [translatedLocalCritical_eq_localTarget s hs he]
  exact localTarget_isRadical

#print axioms actual_selected_coefficient_matrix
#print axioms actual_coefficient_rank
#print axioms targetIdeal_generation
#print axioms translatedLocalCritical_eq_localTarget
#print axioms translatedLocalCritical_eq_axes_intersection
#print axioms translatedLocalCritical_isRadical
end ParametricLocalGeometry
