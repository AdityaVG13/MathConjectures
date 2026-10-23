import LowerChart.ActualCoordinates

namespace ComponentLowerChart
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
noncomputable section

def solvedHub (k : ℕ) : LowerBase k :=
  -(↑((pivotUnit k)⁻¹) : LowerBase k) * algebraMap (LowerParameters k) (LowerBase k) (pivotConstant k)

def forwardCoordinates (k : ℕ) : ActualCoordinates k →ₐ[ℂ] LowerBase k :=
  aeval (fun ij => if h : ij = (0,0) then solvedHub k else
    algebraMap (LowerParameters k) (LowerBase k) (X ⟨ij,h⟩))

@[simp] theorem forwardCoordinates_free (k : ℕ) (p : LowerParameters k) :
    forwardCoordinates k (freeEmbedding k p) = algebraMap (LowerParameters k) (LowerBase k) p := by
  have he : (forwardCoordinates k).comp (freeEmbedding k) =
      Algebra.algHom ℂ (LowerParameters k) (LowerBase k) := by
    ext ij
    simp [forwardCoordinates, freeEmbedding, ij.property]
    rfl
  exact AlgHom.congr_fun he p

@[simp] theorem forwardCoordinates_hub (k : ℕ) : forwardCoordinates k (X (0,0)) = solvedHub k := by
  simp [forwardCoordinates]

theorem pivotUnit_value (k : ℕ) : (pivotUnit k : LowerBase k) =
    algebraMap (LowerParameters k) (LowerBase k) (pivotCoefficient k) := by
  exact IsUnit.unit_spec _

theorem forwardCoordinates_permanent (k : ℕ) : forwardCoordinates k (actualPermanent k) = 0 := by
  rw [actualPermanent_eq, map_add, map_mul, forwardCoordinates_free,
    forwardCoordinates_hub, forwardCoordinates_free, ← pivotUnit_value]
  simp [solvedHub, mul_comm]

def forwardQuotient (k : ℕ) : ActualQuotient k →ₐ[ℂ] LowerBase k :=
  Ideal.Quotient.liftₐ (actualIdeal k) (forwardCoordinates k) (by
    intro p hp
    have hi : actualIdeal k ≤ RingHom.ker (forwardCoordinates k).toRingHom := by
      rw [actualIdeal, Ideal.span_singleton_le_iff_mem]
      exact forwardCoordinates_permanent k
    exact hi hp)

@[simp] theorem forwardQuotient_mk (k : ℕ) (p : ActualCoordinates k) :
    forwardQuotient k (Ideal.Quotient.mk (actualIdeal k) p) = forwardCoordinates k p := rfl

theorem forwardQuotient_pivot_unit (k : ℕ) : IsUnit (forwardQuotient k (quotientPivot k)) := by
  change IsUnit (forwardCoordinates k (actualPivot k))
  rw [actualPivot_eq, forwardCoordinates_free]
  exact IsLocalization.Away.algebraMap_isUnit (S := LowerBase k) (pivotCoefficient k)

def actualForward (k : ℕ) : ActualLowerChart k →ₐ[ℂ] LowerBase k :=
  IsLocalization.Away.liftAlgHom (quotientPivot k) (forwardQuotient_pivot_unit k)

@[simp] theorem actualForward_algebraMap (k : ℕ) (p : ActualQuotient k) :
    actualForward k (algebraMap (ActualQuotient k) (ActualLowerChart k) p) = forwardQuotient k p := by
  exact IsLocalization.Away.lift_eq (quotientPivot k) (forwardQuotient_pivot_unit k) p

def actualCoordinateMap (k : ℕ) : ActualCoordinates k →ₐ[ℂ] ActualLowerChart k :=
  (Algebra.algHom ℂ (ActualQuotient k) (ActualLowerChart k)).comp
    (Ideal.Quotient.mkₐ ℂ (actualIdeal k))

def backwardParameters (k : ℕ) : LowerParameters k →ₐ[ℂ] ActualLowerChart k :=
  (actualCoordinateMap k).comp (freeEmbedding k)

theorem backwardParameters_pivot_unit (k : ℕ) : IsUnit (backwardParameters k (pivotCoefficient k)) := by
  change IsUnit (algebraMap (ActualQuotient k) (ActualLowerChart k)
    (Ideal.Quotient.mk (actualIdeal k) (freeEmbedding k (pivotCoefficient k))))
  rw [← actualPivot_eq]
  exact IsLocalization.Away.algebraMap_isUnit (S := ActualLowerChart k) (quotientPivot k)

def actualBackward (k : ℕ) : LowerBase k →ₐ[ℂ] ActualLowerChart k :=
  IsLocalization.Away.liftAlgHom (pivotCoefficient k) (backwardParameters_pivot_unit k)

@[simp] theorem actualBackward_algebraMap (k : ℕ) (p : LowerParameters k) :
    actualBackward k (algebraMap (LowerParameters k) (LowerBase k) p) = backwardParameters k p := by
  exact IsLocalization.Away.lift_eq (pivotCoefficient k) (backwardParameters_pivot_unit k) p

end
end ComponentLowerChart
#print axioms ComponentLowerChart.actualForward
#print axioms ComponentLowerChart.actualBackward
