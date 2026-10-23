import AffineHessian.ChainRule
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ComponentAffineHessian
open MvPolynomial
variable {σ τ : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq τ]

theorem eval_substitution (phi : σ → MvPolynomial τ ℂ) (a : σ → ℂ)
    (hv : ∀ s, eval (fun _ => 0) (phi s) = a s) (f : MvPolynomial σ ℂ) :
    eval (fun _ => 0) (aeval phi f) = eval a f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf => simp only [map_mul, aeval_X, eval_X, hf, hv]

/-- Exact affine-substitution Hessian chain rule. Its hypotheses are checked
polynomial derivatives and values, not an assumed Hessian identity. -/
theorem hessian_sum (f : MvPolynomial σ ℂ) (phi : σ → MvPolynomial τ ℂ)
    (a : σ → ℂ) (E : Matrix σ τ ℂ)
    (hv : ∀ s, eval (fun _ => 0) (phi s) = a s)
    (hd : ∀ s t, pderiv t (phi s) = C (E s t)) (i j : τ) :
    eval (fun _ => 0) (pderiv j (pderiv i (aeval phi f))) =
      ∑ s : σ, ∑ t : σ, E s i * E t j * eval a (pderiv t (pderiv s f)) := by
  rw [chain_rule f phi i]
  simp_rw [hd]
  rw [map_sum]
  simp_rw [pderiv_C_mul, chain_rule, hd]
  simp only [map_sum, map_mul, eval_C, eval_substitution phi a hv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

#print axioms hessian_sum
end ComponentAffineHessian
