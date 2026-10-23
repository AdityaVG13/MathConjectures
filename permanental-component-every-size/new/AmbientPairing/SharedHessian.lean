import AmbientPairing.SharedRestriction
import AffineHessian.Hessian

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace AmbientPairing
open MvPolynomial ComponentChartJacobian ComponentAmbientHessian
noncomputable section

theorem shared_lower_hessian (k : ℕ) (a b : Fin (k+1)) :
    (∑ c : Fin 3, ∑ d : Fin 3,
      ComponentUpperSeed.k c * ComponentUpperSeed.k d *
        hessian k (lVar (a,c)) (lVar (b,d))) =
    eval (fun _ => 0) (pderiv b (pderiv a
      (AmbientRestriction.ambientPolynomial ComponentUpperSeed.U ComponentUpperSeed.v
        ComponentUpperSeed.k (seedLambda k) (SparseSeed.finArrowhead k)))) := by
  have hh := ComponentAffineHessian.hessian_sum (actualPolynomial k)
    (lowerSubstitution k) (seed k) (lowerDirection k)
    (lowerSubstitution_eval_zero k) (lowerSubstitution_derivative k) a b
  rw [shared_lower_restriction] at hh
  rw [hh]
  simp [lowerDirection, Fintype.sum_sum_type, Fintype.sum_prod_type,
    mul_ite, ite_mul, Finset.sum_ite_irrel, hessian, lVar]

#print axioms shared_lower_hessian
end
end AmbientPairing
