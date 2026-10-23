import GaugeRingEquivalence
import PrimitiveFamily
import Mathlib.RingTheory.Localization.AtPrime.Basic

namespace PermanentGauge.Coordinates
open MvPolynomial

theorem family_pivot (s : ℂ) (k : Fin 9) :
    PrimitiveFamily.A s (pivot k).1 (pivot k).2 = 1 := by
  fin_cases k <;> simp [pivot, PrimitiveFamily.A]

noncomputable def pointPoly (s : ℂ) : P →+* ℂ :=
  eval₂Hom (RingHom.id ℂ) (fun ij => PrimitiveFamily.A s ij.1 ij.2)

theorem pointPoly_delta (s : ℂ) : pointPoly s delta = 1 := by
  simp [pointPoly, delta, family_pivot]

noncomputable def pointMap (s : ℂ) : A →+* ℂ :=
  IsLocalization.Away.lift delta (show IsUnit (pointPoly s delta) by
    rw [pointPoly_delta]; exact isUnit_one)

theorem pointMap_matrix (s : ℂ) (i j : Fin 5) :
    pointMap s (matrix i j) = PrimitiveFamily.A s i j := by
  simp [pointMap, matrix, pointPoly]

theorem pointMap_units (s : ℂ) (k : Fin 9) :
    Units.map (pointMap s : A →* ℂ) (units k) = 1 := by
  apply Units.ext
  change pointMap s (units k : A) = 1
  rw [units_value, pointMap_matrix, family_pivot]

theorem pointMap_rowFactor (s : ℂ) (i : Fin 5) :
    Units.map (pointMap s : A →* ℂ) (rowFactor units i) = 1 := by
  fin_cases i <;> simp [rowFactor, pointMap_units]
theorem pointMap_colFactor (s : ℂ) (i : Fin 5) :
    Units.map (pointMap s : A →* ℂ) (colFactor units i) = 1 := by
  fin_cases i <;> simp [colFactor, pointMap_units]

theorem pointMap_clearPivots (s : ℂ) (i j : Fin 5) :
    pointMap s (clearPivots matrix i j) = PrimitiveFamily.A s i j := by
  classical
  by_cases h : IsPivot (i,j)
  · have ha : PrimitiveFamily.A s i j = 1 := by
      obtain ⟨k, hk⟩ := h
      simpa [hk] using family_pivot s k
    simp [clearPivots, h, ha]
  · simp [clearPivots, h, pointMap_matrix]

theorem pointMap_forwardImage (s : ℂ) (ij : Index) :
    pointMap s (forwardImage ij) = PrimitiveFamily.A s ij.1 ij.2 := by
  classical
  have hr := congrArg (fun v : ℂˣ => (v : ℂ)) (pointMap_rowFactor s ij.1)
  have hc := congrArg (fun v : ℂˣ => (v : ℂ)) (pointMap_colFactor s ij.2)
  change pointMap s (rowFactor units ij.1 : A) = 1 at hr
  change pointMap s (colFactor units ij.2 : A) = 1 at hc
  unfold forwardImage
  split_ifs <;> simp [normalize, scaleMatrix, hr, hc, pointMap_matrix]

theorem pointMap_inverseImage (s : ℂ) (ij : Index) :
    pointMap s (inverseImage ij) = PrimitiveFamily.A s ij.1 ij.2 := by
  have hr : Units.map (pointMap s : A →* ℂ) ((rowFactor units ij.1)⁻¹) = 1 := by
    simp [pointMap_rowFactor]
  have hc : Units.map (pointMap s : A →* ℂ) ((colFactor units ij.2)⁻¹) = 1 := by
    simp [pointMap_colFactor]
  have hr' := congrArg (fun v : ℂˣ => (v : ℂ)) hr
  have hc' := congrArg (fun v : ℂˣ => (v : ℂ)) hc
  change pointMap s (((rowFactor units ij.1)⁻¹ : Aˣ) : A) = 1 at hr'
  change pointMap s (((colFactor units ij.2)⁻¹ : Aˣ) : A) = 1 at hc'
  simp [inverseImage, reconstruct, scaleMatrix, hr', hc', pointMap_clearPivots]

theorem pointMap_comp_forward (s : ℂ) : (pointMap s).comp forwardMap = pointMap s := by
  apply IsLocalization.ringHom_ext (Submonoid.powers delta)
  apply MvPolynomial.ringHom_ext
  · intro a
    change pointMap s (forwardMap (algebraMap P A (C a))) = pointMap s (algebraMap P A (C a))
    rw [forwardMap_constant]
  · intro ij
    change pointMap s (forwardMap (matrix ij.1 ij.2)) = pointMap s (matrix ij.1 ij.2)
    rw [forwardMap_matrix, pointMap_matrix]
    exact pointMap_forwardImage s ij

theorem pointMap_comp_inverse (s : ℂ) : (pointMap s).comp inverseMap = pointMap s := by
  apply IsLocalization.ringHom_ext (Submonoid.powers delta)
  apply MvPolynomial.ringHom_ext
  · intro a
    change pointMap s (inverseMap (algebraMap P A (C a))) = pointMap s (algebraMap P A (C a))
    rw [inverseMap_constant]
  · intro ij
    change pointMap s (inverseMap (matrix ij.1 ij.2)) = pointMap s (matrix ij.1 ij.2)
    rw [inverseMap_matrix, pointMap_matrix]
    exact pointMap_inverseImage s ij

noncomputable def pointIdeal (s : ℂ) : Ideal A := RingHom.ker (pointMap s)
instance pointIdeal_prime (s : ℂ) : (pointIdeal s).IsPrime := RingHom.ker_isPrime (pointMap s)

theorem pointIdeal_comap_forward (s : ℂ) : (pointIdeal s).comap forwardMap = pointIdeal s := by
  change RingHom.ker ((pointMap s).comp forwardMap) = RingHom.ker (pointMap s)
  rw [pointMap_comp_forward]
theorem pointIdeal_comap_inverse (s : ℂ) : (pointIdeal s).comap inverseMap = pointIdeal s := by
  change RingHom.ker ((pointMap s).comp inverseMap) = RingHom.ker (pointMap s)
  rw [pointMap_comp_inverse]

#print axioms pointMap_comp_forward
#print axioms pointIdeal_comap_inverse
end PermanentGauge.Coordinates
