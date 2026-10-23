import GaugeFamilyPoint

namespace PermanentGauge.Coordinates

abbrev LocalAt (s : ℂ) := Localization.AtPrime (pointIdeal s)

/-- The actual local-ring coordinate equivalence at A(s), in the open chart
where all nine fixed pivot entries are units. No restriction on s is required. -/
noncomputable def localReconstructEquiv (s : ℂ) : LocalAt s ≃+* LocalAt s :=
  Localization.localRingEquiv (pointIdeal s) (pointIdeal s) coordinateRingEquiv.symm
    (by change pointIdeal s = (pointIdeal s).comap inverseMap
        exact (pointIdeal_comap_inverse s).symm)

theorem localReconstruct_toMap (s : ℂ) (x : A) :
    localReconstructEquiv s (algebraMap A (LocalAt s) x) =
      algebraMap A (LocalAt s) (inverseMap x) := by
  exact Localization.localRingHom_to_map (pointIdeal s) (pointIdeal s)
    coordinateRingEquiv.symm.toRingHom (by
      change pointIdeal s = (pointIdeal s).comap inverseMap
      exact (pointIdeal_comap_inverse s).symm) x

noncomputable def localAmbientIdeal (s : ℂ) : Ideal (LocalAt s) :=
  Ideal.map (algebraMap A (LocalAt s)) (cofactorIdeal matrix)
noncomputable def localNormalizedIdeal (s : ℂ) : Ideal (LocalAt s) :=
  Ideal.map (algebraMap A (LocalAt s)) (cofactorIdeal (clearPivots matrix))

/-- Exact transport of the actual localized25-cofactor ideal. The normalized
ideal still needs to be matched to the existing16-variable reconstructed chart. -/
theorem local_cofactor_transport (s : ℂ) :
    Ideal.map (localReconstructEquiv s).toRingHom (localAmbientIdeal s) =
      localNormalizedIdeal s := by
  unfold localAmbientIdeal localNormalizedIdeal
  rw [Ideal.map_map]
  have he : (localReconstructEquiv s).toRingHom.comp (algebraMap A (LocalAt s)) =
      (algebraMap A (LocalAt s)).comp inverseMap := by
    apply RingHom.ext
    intro x
    exact localReconstruct_toMap s x
  rw [he, ← Ideal.map_map, inverseMap_cofactorIdeal]

#print axioms localReconstructEquiv
#print axioms local_cofactor_transport
end PermanentGauge.Coordinates
