import AmbientHessianBlocks.ZeroLowerLeft

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ComponentAmbientHessian
noncomputable section
open MvPolynomial Matrix Equiv ComponentChartJacobian

@[simp] theorem nonLower_b {k : ℕ} (b : BIndex) : NonLower (bVar (k:=k) b) := by
  intro a; simp [lVar,bVar]
@[simp] theorem nonLower_w {k : ℕ} (w : WIndex k) : NonLower (wVar w) := by
  intro a; simp [lVar,wVar]
@[simp] theorem nonLower_v {k : ℕ} (v : VIndex k) : NonLower (vVar v) := by
  intro a; simp [lVar,vVar]

theorem deriv_upper_w (k : ℕ) (w : WIndex k) : pderiv (wVar w) (blockU k).permanent = 0 := by
  apply ExceptionalCofactorDerivative.permanent_derivative_zero
  intro i j
  simp [blockU, blockB, Matrix.submatrix, bVar, wVar, pderiv_X]

theorem deriv_upper_v (k : ℕ) (v : VIndex k) : pderiv (vVar v) (blockU k).permanent = 0 := by
  apply ExceptionalCofactorDerivative.permanent_derivative_zero
  intro i j
  simp [blockU, blockB, Matrix.submatrix, bVar, vVar, pderiv_X]

theorem deriv_lower_b (k : ℕ) (b : BIndex) : pderiv (bVar b) (blockW k).permanent = 0 := by
  apply ExceptionalCofactorDerivative.permanent_derivative_zero
  intro i j
  simp [blockW, bVar, wVar, pderiv_X]

theorem deriv_lower_v (k : ℕ) (v : VIndex k) : pderiv (vVar v) (blockW k).permanent = 0 := by
  apply ExceptionalCofactorDerivative.permanent_derivative_zero
  intro i j
  simp [blockW, vVar, wVar, pderiv_X]

theorem eval_upper_zero (k : ℕ) : eval (seed k) (blockU k).permanent = 0 := by
  rw [← upperPolynomial_last]
  exact generator_vanishes_at_seed k (Sum.inl 3)

theorem eval_lower_zero (k : ℕ) : eval (seed k) (blockW k).permanent = 0 := by
  rw [← lowerPolynomial_actual]
  exact generator_vanishes_at_seed k (Sum.inr (Sum.inl ()))

/-- All upper-B versus upper-B Hessian entries vanish at the actual seed. -/
theorem hessian_b_b (k : ℕ) (b c : BIndex) : hessian k (bVar b) (bVar c) = 0 := by
  rw [hessian_nonLower _ _ (nonLower_b b) (nonLower_b c)]
  simp only [pderiv_mul, deriv_lower_b, mul_zero, add_zero]
  simp [eval_lower_zero]

/-- All lower-W versus lower-W Hessian entries vanish at the actual seed. -/
theorem hessian_w_w (k : ℕ) (b c : WIndex k) : hessian k (wVar b) (wVar c) = 0 := by
  rw [hessian_nonLower _ _ (nonLower_w b) (nonLower_w c)]
  simp only [pderiv_mul, deriv_upper_w, zero_mul, zero_add]
  simp [eval_upper_zero]

/-- Every extra upper-right direction has zero pairing with every non-L direction. -/
theorem hessian_v_nonLower (k : ℕ) (v : VIndex k) (x : Variables k) (hx : NonLower x) :
    hessian k (vVar v) x = 0 := by
  rw [hessian_nonLower _ _ (nonLower_v v) hx]
  simp [pderiv_mul, deriv_upper_v, deriv_lower_v]

/-- The U-W pairing is the outer product of the two permanent gradients. -/
theorem hessian_b_w (k : ℕ) (b : BIndex) (w : WIndex k) :
    hessian k (bVar b) (wVar w) =
      eval (seed k) (pderiv (bVar b) (blockU k).permanent) *
      eval (seed k) (pderiv (wVar w) (blockW k).permanent) := by
  rw [hessian_nonLower _ _ (nonLower_b b) (nonLower_w w)]
  have hz : pderiv (wVar w) (pderiv (bVar b) (blockU k).permanent) = 0 := by
    rw [pderiv_comm, deriv_upper_w, map_zero]
  simp [pderiv_mul, deriv_lower_b, hz]

/-- In the four selected upper directions, pairing with W00 is precisely the
row of the already verified upper Jacobian corresponding to per U. -/
theorem hessian_selected_b_w00 (k : ℕ) (c : Fin 4) :
    hessian k (bVar (ComponentUpperSeed.selected c)) (wVar (0,0)) =
      ComponentUpperSeed.jac 3 c := by
  rw [hessian_b_w, ← upperPolynomial_last, ← lowerPolynomial_actual]
  have hu := upper_upper k 3 c
  have hw := lower_lower k
  change eval (seed k) (pderiv (bVar (ComponentUpperSeed.selected c)) (upperPolynomial k 3)) = _ at hu
  change eval (seed k) (pderiv (wVar (0,0)) (lowerPolynomial k)) = 1 at hw
  rw [hu, hw, mul_one]

#print axioms hessian_b_b
#print axioms hessian_w_w
#print axioms hessian_v_nonLower
#print axioms hessian_selected_b_w00
end
end ComponentAmbientHessian
