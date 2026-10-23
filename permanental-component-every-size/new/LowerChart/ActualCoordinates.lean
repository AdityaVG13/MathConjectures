import LowerChart.UniformPivot
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace ComponentLowerChart
open MvPolynomial Matrix
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev ActualCoordinates (k : ℕ) := MvPolynomial (LowerIndex k) ℂ

def actualMatrix (k : ℕ) : Matrix (Fin (k+1)) (Fin (k+1)) (ActualCoordinates k) :=
  fun i j => X (i,j)

def actualPermanent (k : ℕ) : ActualCoordinates k := (actualMatrix k).permanent

def actualPivot (k : ℕ) : ActualCoordinates k :=
  ((actualMatrix k).submatrix (0 : Fin (k+1)).succAbove (0 : Fin (k+1)).succAbove).permanent

def freeEmbedding (k : ℕ) : LowerParameters k →ₐ[ℂ] ActualCoordinates k := rename Subtype.val

def actualIdeal (k : ℕ) : Ideal (ActualCoordinates k) := Ideal.span {actualPermanent k}
abbrev ActualQuotient (k : ℕ) := ActualCoordinates k ⧸ actualIdeal k

def quotientPivot (k : ℕ) : ActualQuotient k := Ideal.Quotient.mk _ (actualPivot k)
abbrev ActualLowerChart (k : ℕ) := Localization.Away (quotientPivot k)

theorem actualPivot_eq (k : ℕ) : actualPivot k = freeEmbedding k (pivotCoefficient k) := by
  unfold actualPivot pivotCoefficient
  have hm : (((zeroHub k).submatrix (0 : Fin (k+1)).succAbove
      (0 : Fin (k+1)).succAbove).map (freeEmbedding k)).permanent =
      freeEmbedding k (((zeroHub k).submatrix (0 : Fin (k+1)).succAbove
      (0 : Fin (k+1)).succAbove).permanent) :=
    ComponentFamilyContainment.permanent_map (freeEmbedding k).toRingHom _
  rw [← hm]
  congr 1
  ext i j
  simp [Matrix.map_apply, Matrix.submatrix, zeroHub, actualMatrix, freeEmbedding]

theorem actualMatrix_entryUpdate (k : ℕ) :
    actualMatrix k = entryUpdate ((zeroHub k).map (freeEmbedding k)) 0 0 (X (0,0)) := by
  ext i j
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    simp_all [entryUpdate, Matrix.map_apply, Matrix.updateRow_apply, zeroHub,
      actualMatrix, freeEmbedding, Function.update]

theorem actualPermanent_eq (k : ℕ) : actualPermanent k =
    freeEmbedding k (pivotConstant k) + X (0,0) * freeEmbedding k (pivotCoefficient k) := by
  unfold actualPermanent
  rw [actualMatrix_entryUpdate, permanent_entryUpdate]
  have hc : (((zeroHub k).map (freeEmbedding k)).submatrix
      (0 : Fin (k+1)).succAbove (0 : Fin (k+1)).succAbove).permanent =
      freeEmbedding k (pivotCoefficient k) :=
    ComponentFamilyContainment.permanent_map (freeEmbedding k).toRingHom _
  have hm : ((zeroHub k).map (freeEmbedding k)).permanent =
      freeEmbedding k (pivotConstant k) :=
    ComponentFamilyContainment.permanent_map (freeEmbedding k).toRingHom _
  rw [hc, hm]
  simp [pivotConstant, Matrix.map_apply, zeroHub]

end
end ComponentLowerChart
#print axioms ComponentLowerChart.actualPermanent_eq
