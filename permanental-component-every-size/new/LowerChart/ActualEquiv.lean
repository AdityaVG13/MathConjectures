import LowerChart.ActualMaps

namespace ComponentLowerChart
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
noncomputable section

@[simp] theorem actualForward_coordinateMap (k : ℕ) (p : ActualCoordinates k) :
    actualForward k (actualCoordinateMap k p) = forwardCoordinates k p := by
  change actualForward k (algebraMap (ActualQuotient k) (ActualLowerChart k)
    (Ideal.Quotient.mk (actualIdeal k) p)) = _
  rw [actualForward_algebraMap, forwardQuotient_mk]

theorem actualCoordinateMap_permanent (k : ℕ) : actualCoordinateMap k (actualPermanent k) = 0 := by
  have hq : Ideal.Quotient.mk (actualIdeal k) (actualPermanent k) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton _)
  change algebraMap (ActualQuotient k) (ActualLowerChart k)
    (Ideal.Quotient.mk (actualIdeal k) (actualPermanent k)) = 0
  rw [hq, map_zero]

theorem actualBackward_forward_hub (k : ℕ) :
    actualBackward k (forwardCoordinates k (X (0,0))) = actualCoordinateMap k (X (0,0)) := by
  apply (backwardParameters_pivot_unit k).mul_right_cancel
  have h1 := actualCoordinateMap_permanent k
  rw [actualPermanent_eq, map_add, map_mul] at h1
  have h2 := congrArg (actualBackward k) (forwardCoordinates_permanent k)
  simp only [actualPermanent_eq, map_add, map_mul, forwardCoordinates_free,
    actualBackward_algebraMap, map_zero] at h2
  change backwardParameters k (pivotConstant k) +
    actualBackward k (forwardCoordinates k (X (0,0))) * backwardParameters k (pivotCoefficient k) = 0 at h2
  change backwardParameters k (pivotConstant k) +
    actualCoordinateMap k (X (0,0)) * backwardParameters k (pivotCoefficient k) = 0 at h1
  exact add_left_cancel (h2.trans h1.symm)

theorem actualBackward_forward_coordinates (k : ℕ) :
    (actualBackward k).comp (forwardCoordinates k) = actualCoordinateMap k := by
  ext ij
  by_cases hij : ij = (0,0)
  · subst ij
    exact actualBackward_forward_hub k
  · change actualBackward k (forwardCoordinates k (X ij)) = actualCoordinateMap k (X ij)
    have he : (X ij : ActualCoordinates k) = freeEmbedding k (X ⟨ij,hij⟩) := by
      simp [freeEmbedding]
    rw [he, forwardCoordinates_free, actualBackward_algebraMap]
    rfl

theorem actualForward_backward (k : ℕ) :
    (actualForward k).comp (actualBackward k) = AlgHom.id ℂ (LowerBase k) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (pivotCoefficient k))
  ext ij
  change actualForward k (actualBackward k
    (algebraMap (LowerParameters k) (LowerBase k) (X ij))) =
      algebraMap (LowerParameters k) (LowerBase k) (X ij)
  rw [actualBackward_algebraMap]
  change actualForward k (actualCoordinateMap k (freeEmbedding k (X ij))) = _
  rw [actualForward_coordinateMap, forwardCoordinates_free]

theorem actualBackward_forward (k : ℕ) :
    (actualBackward k).comp (actualForward k) = AlgHom.id ℂ (ActualLowerChart k) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (quotientPivot k))
  apply Ideal.Quotient.algHom_ext
  ext ij
  change actualBackward k (actualForward k
    (algebraMap (ActualQuotient k) (ActualLowerChart k)
      (Ideal.Quotient.mk (actualIdeal k) (X ij)))) = actualCoordinateMap k (X ij)
  rw [actualForward_algebraMap, forwardQuotient_mk]
  exact AlgHom.congr_fun (actualBackward_forward_coordinates k) (X ij)

/-- The actual generic-W hypersurface, localized at its actual 00 cofactor,
is isomorphic as a complex algebra to the localization of the free nonhub coordinates. -/
def actualLowerChartEquiv (k : ℕ) : ActualLowerChart k ≃ₐ[ℂ] LowerBase k :=
  AlgEquiv.ofAlgHom (actualForward k) (actualBackward k)
    (actualForward_backward k) (actualBackward_forward k)

end
end ComponentLowerChart
#print axioms ComponentLowerChart.actualLowerChartEquiv
