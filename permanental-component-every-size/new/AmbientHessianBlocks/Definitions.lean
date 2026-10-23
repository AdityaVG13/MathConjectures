import ChartJacobian.ChartIdealBridge

set_option autoImplicit false
namespace ComponentAmbientHessian
noncomputable section
open MvPolynomial Matrix Equiv ComponentChartJacobian

def actualPolynomial (k : ℕ) : P k := (actualAmbient k).permanent

def hessian (k : ℕ) (x y : Variables k) : ℂ :=
  eval (seed k) (pderiv y (pderiv x (actualPolynomial k)))

theorem hessian_symmetric (k : ℕ) (x y : Variables k) : hessian k x y = hessian k y x := by
  unfold hessian
  rw [pderiv_comm]

end
end ComponentAmbientHessian
