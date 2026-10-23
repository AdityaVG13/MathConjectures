import FullHessianRank.ActualLowerBound
import FullHessianRank.SaturatedJacobianRank

set_option autoImplicit false
namespace ComponentFullHessianRank
noncomputable section
open Matrix MvPolynomial ComponentChartJacobian ComponentAmbientHessian

/-- Local containment suffices; global polynomial-ideal containment is neither
assumed nor claimed for the open chart. -/
theorem actual_ambient_rank_eq_of_local_membership (k : ℕ)
    (hmem : ∀ i : Variables k, ∃ s : P k, eval (seed k) s ≠ 0 ∧
      s * pderiv i (actualPolynomial k) ∈ Ideal.span (Set.range (generator k))) :
    Matrix.rank (hessian k) = 5 * (k + 1) + 3 := by
  apply le_antisymm _ (actual_ambient_rank_lower_bound k)
  have hh := jacobian_rank_le_of_local_membership (seed k)
    (fun i => pderiv i (actualPolynomial k)) (generator k)
    (generator_vanishes_at_seed k) hmem
  rw [generator_count] at hh
  exact hh

#print axioms actual_ambient_rank_eq_of_local_membership
end
end ComponentFullHessianRank
