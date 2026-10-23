import LowerChart.ActualEquiv
import GeneralLaplace.GeneralLaplace

namespace ComponentLowerChart
open MvPolynomial Matrix
set_option backward.isDefEq.respectTransparency false
noncomputable section

def actualSeedCoordinates (k : ℕ) : ActualCoordinates k →ₐ[ℂ] ℂ :=
  aeval (fun ij => SparseSeed.finArrowhead k ij.1 ij.2)

theorem actualSeed_permanent (k : ℕ) : actualSeedCoordinates k (actualPermanent k) = 0 := by
  have he : actualSeedCoordinates k (actualPermanent k) = (SparseSeed.finArrowhead k).permanent := by
    simp [actualSeedCoordinates, actualPermanent, actualMatrix, Matrix.permanent]
  rw [he, SparseSeed.finArrowhead, ComponentGeneralLaplace.permanent_reindex,
    SparseSeed.permanent_arrowhead]

theorem actualSeed_pivot (k : ℕ) : actualSeedCoordinates k (actualPivot k) = 1 := by
  have he : actualSeedCoordinates k (actualPivot k) =
      ((SparseSeed.finArrowhead k).submatrix (0 : Fin (k+1)).succAbove
        (0 : Fin (k+1)).succAbove).permanent := by
    simp [actualSeedCoordinates, actualPivot, actualMatrix, Matrix.permanent, Matrix.submatrix]
  rw [he, SparseSeed.fin_cofactor_eq]
  simp [SparseSeed.cofactor_formula]

def actualQuotientSeed (k : ℕ) : ActualQuotient k →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ (actualIdeal k) (actualSeedCoordinates k) (by
    intro p hp
    have hi : actualIdeal k ≤ RingHom.ker (actualSeedCoordinates k).toRingHom := by
      rw [actualIdeal, Ideal.span_singleton_le_iff_mem]
      exact actualSeed_permanent k
    exact hi hp)

@[simp] theorem actualQuotientSeed_mk (k : ℕ) (p : ActualCoordinates k) :
    actualQuotientSeed k (Ideal.Quotient.mk (actualIdeal k) p) = actualSeedCoordinates k p := rfl

@[simp] theorem actualQuotientSeed_pivot (k : ℕ) : actualQuotientSeed k (quotientPivot k) = 1 :=
  actualSeed_pivot k

def actualLowerChartSeed (k : ℕ) : ActualLowerChart k →ₐ[ℂ] ℂ :=
  IsLocalization.Away.liftAlgHom (quotientPivot k) (by
    rw [actualQuotientSeed_pivot]
    exact isUnit_one)

@[simp] theorem actualLowerChartSeed_algebraMap (k : ℕ) (p : ActualQuotient k) :
    actualLowerChartSeed k (algebraMap (ActualQuotient k) (ActualLowerChart k) p) =
      actualQuotientSeed k p := by
  exact IsLocalization.Away.lift_eq (quotientPivot k)
    (show IsUnit (actualQuotientSeed k (quotientPivot k)) by simp) p

end
end ComponentLowerChart
#print axioms ComponentLowerChart.actualQuotientSeed_pivot
#print axioms ComponentLowerChart.actualLowerChartSeed
