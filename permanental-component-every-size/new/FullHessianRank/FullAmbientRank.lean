import FullHessianRank.ActualLocalizedRank
import ActualLocalChart.Containment

set_option autoImplicit false
namespace ComponentFullHessianRank
noncomputable section
open Matrix MvPolynomial ComponentChartJacobian ComponentAmbientHessian
attribute [local instance] RingHom.ker_isPrime

/-- Exact rank of the genuine full ambient permanental Hessian at the explicit
uniform seed. All local membership and Hessian restriction inputs are discharged. -/
theorem actual_ambient_rank (k : ℕ) :
    Matrix.rank (hessian k) = 5 * (k + 1) + 3 := by
  let S := Localization.AtPrime (RingHom.ker (aeval (R := ℂ) (seed k)).toRingHom)
  apply actual_ambient_rank_eq_of_localized_membership k S
  exact ComponentActualLocalChart.actual_local_gradient_membership k S

theorem ambient_variable_count (k : ℕ) : Fintype.card (Variables k) = (k + 4)^2 := by
  rw [Fintype.card_congr (entryEquiv k)]
  simp only [Fintype.card_prod, Axis, Fintype.card_sum, Fintype.card_fin]
  ring

/-- Dimension of the genuine ambient Hessian kernel, with no geometric
identification of that kernel assumed. -/
theorem actual_ambient_kernel_finrank (k : ℕ) :
    Module.finrank ℂ (LinearMap.ker (Matrix.mulVecLin (hessian k))) = k^2 + 3*k + 8 := by
  have hd := (Matrix.mulVecLin (hessian k)).finrank_range_add_finrank_ker
  change Matrix.rank (hessian k) + Module.finrank ℂ (LinearMap.ker (Matrix.mulVecLin (hessian k))) = Module.finrank ℂ (Variables k → ℂ) at hd
  rw [actual_ambient_rank, Module.finrank_pi, ambient_variable_count] at hd
  nlinarith

#print axioms actual_ambient_kernel_finrank
#print axioms actual_ambient_rank
end
end ComponentFullHessianRank
