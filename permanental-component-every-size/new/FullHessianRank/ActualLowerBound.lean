import FullHessianRank.SelectedNonsingular
import AmbientPairing.SharedHessian

set_option autoImplicit false
namespace ComponentFullHessianRank
noncomputable section
open Matrix ComponentChartJacobian ComponentAmbientHessian AmbientPairing

theorem contractedLowerHessian_eq (k : ℕ) : contractedLowerHessian k =
    finAmbientHessian k ComponentUpperSeed.U ComponentUpperSeed.v ComponentUpperSeed.k := by
  ext a b
  exact shared_lower_hessian k a b

/-- The genuine selected normal Hessian is invertible, uniformly in k. -/
theorem actual_selected_isUnit (k : ℕ) :
    IsUnit (Matrix.submatrix (hessian k) (selected k) (selected k)) :=
  actual_selected_isUnit_of_chain_rule k (contractedLowerHessian_eq k)

/-- The genuine full ambient Hessian has the required normal-rank lower bound. -/
theorem actual_ambient_rank_lower_bound (k : ℕ) :
    5 * (k + 1) + 3 ≤ Matrix.rank (hessian k) :=
  actual_rank_lower_bound_of_chain_rule k (contractedLowerHessian_eq k)

theorem actual_selected_det_ne_zero (k : ℕ) :
    (Matrix.submatrix (hessian k) (selected k) (selected k)).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (actual_selected_isUnit k)).ne_zero

/-- The Jacobian of the selected actual gradient equations has full row rank. -/
theorem actual_selected_gradient_jacobian_rank (k : ℕ) :
    Matrix.rank (fun (i : Generators k) (x : Variables k) =>
      MvPolynomial.eval (seed k) (MvPolynomial.pderiv x
        (MvPolynomial.pderiv (selected k i) (actualPolynomial k)))) =
      Fintype.card (Generators k) := by
  let J : Matrix (Generators k) (Variables k) ℂ :=
    Matrix.submatrix (hessian k) (selected k) id
  change J.rank = _
  apply le_antisymm J.rank_le_card_height
  have hh := J.rank_submatrix_le id (selected k)
  have he : J.submatrix id (selected k) = Matrix.submatrix (hessian k) (selected k) (selected k) := rfl
  rw [he, Matrix.rank_of_isUnit _ (actual_selected_isUnit k)] at hh
  exact hh

#print axioms actual_selected_gradient_jacobian_rank
#print axioms actual_selected_isUnit
#print axioms actual_selected_det_ne_zero
#print axioms actual_ambient_rank_lower_bound
end
end ComponentFullHessianRank
