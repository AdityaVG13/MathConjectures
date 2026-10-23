import GaugeMapNaturality
import Mathlib.RingTheory.Ideal.Maps

namespace PermanentGauge.Coordinates
open MvPolynomial

theorem inverse_forward_matrix (i j : Fin 5) :
    inverseMap (forwardMap (matrix i j)) = matrix i j := by
  classical
  rw [forwardMap_matrix]
  unfold forwardImage
  split_ifs with h
  · obtain ⟨k, hk⟩ := h
    have he : inverseMap (matrix (pivot k).1 (pivot k).2) = matrix (pivot k).1 (pivot k).2 := by
      rw [inverseMap_matrix]
      simpa using inverseImage_pivot k
    simpa [hk] using he
  · rw [map_normalize inverseMap inverseMap_units]
    have he : (fun i j => inverseMap (matrix i j)) = reconstruct units (clearPivots matrix) := by
      ext i j
      exact inverseMap_matrix i j
    rw [he, normalize_reconstruct]
    simp [clearPivots, h]

theorem forward_clear_matrix :
    (fun i j => forwardMap (clearPivots matrix i j)) = normalize units matrix := by
  classical
  ext i j
  rw [map_clearPivots]
  by_cases h : IsPivot (i,j)
  · have hn : normalize units matrix i j = 1 := by
      obtain ⟨k, hk⟩ := h
      have he := normalize_pivots units matrix (fun k => (units_value k).symm) k
      simpa [hk] using he
    simp [clearPivots, h, hn]
  · simp [clearPivots, h, forwardMap_matrix, forwardImage]

theorem forward_inverse_matrix (i j : Fin 5) :
    forwardMap (inverseMap (matrix i j)) = matrix i j := by
  rw [inverseMap_matrix]
  change forwardMap (reconstruct units (clearPivots matrix) i j) = _
  rw [map_reconstruct forwardMap forwardMap_units, forward_clear_matrix,
    reconstruct_normalize]

theorem forwardMap_constant (a : ℂ) :
    forwardMap (algebraMap P A (C a)) = algebraMap P A (C a) := by
  simp [forwardMap, forwardPoly]
theorem inverseMap_constant (a : ℂ) :
    inverseMap (algebraMap P A (C a)) = algebraMap P A (C a) := by
  simp [inverseMap, inversePoly]

theorem inverse_comp_forward : inverseMap.comp forwardMap = RingHom.id A := by
  apply IsLocalization.ringHom_ext (Submonoid.powers delta)
  apply MvPolynomial.ringHom_ext
  · intro a
    change inverseMap (forwardMap (algebraMap P A (C a))) = algebraMap P A (C a)
    rw [forwardMap_constant, inverseMap_constant]
  · intro ij
    exact inverse_forward_matrix ij.1 ij.2

theorem forward_comp_inverse : forwardMap.comp inverseMap = RingHom.id A := by
  apply IsLocalization.ringHom_ext (Submonoid.powers delta)
  apply MvPolynomial.ringHom_ext
  · intro a
    change forwardMap (inverseMap (algebraMap P A (C a))) = algebraMap P A (C a)
    rw [inverseMap_constant, forwardMap_constant]
  · intro ij
    exact forward_inverse_matrix ij.1 ij.2

/-- An actual ring equivalence of the open coordinate ring, with explicit
inverse reconstruction. This does not yet transport a chosen local ring. -/
noncomputable def coordinateRingEquiv : A ≃+* A :=
  { forwardMap with
    invFun := inverseMap
    left_inv := fun x => RingHom.congr_fun inverse_comp_forward x
    right_inv := fun x => RingHom.congr_fun forward_comp_inverse x }

/-- The reconstruction map carries the actual ambient cofactor ideal to the
cofactor ideal of the matrix with the nine tree pivots fixed to1. -/
theorem inverseMap_cofactorIdeal :
    Ideal.map inverseMap (cofactorIdeal matrix) = cofactorIdeal (clearPivots matrix) := by
  rw [cofactorIdeal, Ideal.map_span, ← Set.range_comp]
  have he : inverseMap ∘ cofactor matrix = cofactor (fun i j => inverseImage (i,j)) := by
    funext ij
    simp [cofactor, Matrix.permanent, Matrix.submatrix, inverseMap_matrix,
      Function.comp_def]
  rw [he]
  exact inverseImage_cofactorIdeal

#print axioms coordinateRingEquiv
#print axioms inverseMap_cofactorIdeal
end PermanentGauge.Coordinates
