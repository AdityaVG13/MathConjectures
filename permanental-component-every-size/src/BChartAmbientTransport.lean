import BChartRowClearing

set_option autoImplicit false
namespace BChartTransport
open PermanentGauge PermanentGauge.Coordinates

/-- Composition of the actual pivot-gauge reconstruction and the triangular
b-chart translation. Both inverse maps have already been checked. -/
noncomputable def ambientChartEquiv (s : ℂ) (hs : s ≠ 0) :
    LocalAt s ≃+* LocalAt s :=
  (localReconstructEquiv s).trans (translationEquiv s hs 1)

theorem translation_normalized_ideal (s : ℂ) (hs : s ≠ 0) :
    Ideal.map (translationEquiv s hs 1).toRingHom (localNormalizedIdeal s) =
      localClearedIdeal s := by
  have hn : localNormalizedIdeal s = cofactorIdeal (localNormalizedMatrix s) := by
    exact cofactorIdeal_map (algebraMap A (LocalAt s)) (clearPivots matrix)
  rw [hn, cofactorIdeal_map]
  exact translated_cofactorIdeal s hs

/-- The actual ambient cofactor ideal in the nine-pivot open local ring is
carried to the explicit base-changed target ideal, for every nonzero complex
parameter. No radicality or component claim is inferred merely from base change. -/
theorem ambient_cofactor_normal_form (s : ℂ) (hs : s ≠ 0) :
    Ideal.map (ambientChartEquiv s hs).toRingHom (localAmbientIdeal s) =
      localExpectedIdeal s := by
  change Ideal.map ((translationEquiv s hs 1).toRingHom.comp
    (localReconstructEquiv s).toRingHom) (localAmbientIdeal s) = _
  rw [← Ideal.map_map, local_cofactor_transport,
    translation_normalized_ideal, localCleared_eq_expected s hs]

#print axioms ambientChartEquiv
#print axioms ambient_cofactor_normal_form
end BChartTransport
