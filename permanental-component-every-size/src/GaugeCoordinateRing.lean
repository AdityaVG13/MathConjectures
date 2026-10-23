import NinePivotEquivalence
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Basic.Complex.Basic

namespace PermanentGauge.Coordinates
open MvPolynomial
abbrev Index := Fin 5 × Fin 5
abbrev P := MvPolynomial Index ℂ
noncomputable def delta : P := ∏ k : Fin 9, X (pivot k)
abbrev A := Localization.Away delta
noncomputable def matrix : Matrix (Fin 5) (Fin 5) A :=
  fun i j => algebraMap P A (X (i,j))

theorem pivot_isUnit (k : Fin 9) : IsUnit (matrix (pivot k).1 (pivot k).2) := by
  apply IsLocalization.Away.isUnit_of_dvd delta
  exact Finset.dvd_prod_of_mem (fun k : Fin 9 => (X (pivot k) : P)) (Finset.mem_univ k)

noncomputable def units : Fin 9 → Aˣ := fun k => (pivot_isUnit k).unit

theorem units_value (k : Fin 9) : (units k : A) = matrix (pivot k).1 (pivot k).2 :=
  (pivot_isUnit k).unit_spec

def IsPivot (ij : Index) : Prop := ∃ k : Fin 9, pivot k = ij
noncomputable def clearPivots (M : Matrix (Fin 5) (Fin 5) A) : Matrix (Fin 5) (Fin 5) A :=
  by
    classical
    exact fun i j => if IsPivot (i,j) then 1 else M i j

theorem clearPivots_at (M : Matrix (Fin 5) (Fin 5) A) (k : Fin 9) :
    clearPivots M (pivot k).1 (pivot k).2 = 1 := by
  simp [clearPivots, IsPivot]

noncomputable def forwardImage (ij : Index) : A :=
  by
    classical
    exact if IsPivot ij then matrix ij.1 ij.2 else normalize units matrix ij.1 ij.2
noncomputable def inverseImage (ij : Index) : A :=
  reconstruct units (clearPivots matrix) ij.1 ij.2

theorem forwardImage_pivot (k : Fin 9) : forwardImage (pivot k) = matrix (pivot k).1 (pivot k).2 := by
  simp [forwardImage, IsPivot]

theorem inverseImage_pivot (k : Fin 9) : inverseImage (pivot k) = matrix (pivot k).1 (pivot k).2 := by
  rw [inverseImage, reconstruct_pivots units (clearPivots matrix) (clearPivots_at matrix), units_value]

noncomputable def forwardPoly : P →+* A :=
  eval₂Hom ((algebraMap P A).comp C) forwardImage
noncomputable def inversePoly : P →+* A :=
  eval₂Hom ((algebraMap P A).comp C) inverseImage

theorem forwardPoly_delta : forwardPoly delta = algebraMap P A delta := by
  simp [delta, forwardPoly, forwardImage_pivot, matrix]

theorem inversePoly_delta : inversePoly delta = algebraMap P A delta := by
  simp [delta, inversePoly, inverseImage_pivot, matrix]

noncomputable def forwardMap : A →+* A :=
  IsLocalization.Away.lift delta (show IsUnit (forwardPoly delta) by
    rw [forwardPoly_delta]
    exact IsLocalization.Away.algebraMap_isUnit delta)
noncomputable def inverseMap : A →+* A :=
  IsLocalization.Away.lift delta (show IsUnit (inversePoly delta) by
    rw [inversePoly_delta]
    exact IsLocalization.Away.algebraMap_isUnit delta)

theorem forwardMap_matrix (i j : Fin 5) : forwardMap (matrix i j) = forwardImage (i,j) := by
  simp [forwardMap, matrix, forwardPoly]
theorem inverseMap_matrix (i j : Fin 5) : inverseMap (matrix i j) = inverseImage (i,j) := by
  simp [inverseMap, matrix, inversePoly]

/-- Actual cofactor ideals after the proposed reconstruction map. The existence
of inverse ring maps is a separate obligation, not assumed here. -/
theorem inverseImage_cofactorIdeal :
    cofactorIdeal (fun i j => inverseImage (i,j)) = cofactorIdeal (clearPivots matrix) := by
  exact cofactorIdeal_scaleMatrix (fun i => (rowFactor units i)⁻¹)
    (fun j => (colFactor units j)⁻¹) (clearPivots matrix)

#print axioms forwardMap_matrix
#print axioms inverseMap_matrix
#print axioms inverseImage_cofactorIdeal
end PermanentGauge.Coordinates
