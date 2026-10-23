import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ComponentAffineHessian
open MvPolynomial
variable {σ τ : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq τ]

theorem chain_rule (f : MvPolynomial σ ℂ) (phi : σ → MvPolynomial τ ℂ) (t : τ) :
    pderiv t (aeval phi f) =
      ∑ s : σ, pderiv t (phi s) * aeval phi (pderiv s f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add, hf, hg, mul_add, Finset.sum_add_distrib]
  | mul_X f i hf =>
    have hX (s : σ) : aeval phi (pderiv s (X i : MvPolynomial σ ℂ)) =
        if s = i then 1 else 0 := by
      by_cases hs : s = i
      · subst s; simp
      · simp [pderiv_X, Pi.single_apply, hs, Ne.symm hs]
    simp only [map_mul, aeval_X, pderiv_mul, hf, map_add, hX,
      mul_add, Finset.sum_add_distrib]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro s _
      ring
    · ring

#print axioms chain_rule
end ComponentAffineHessian
