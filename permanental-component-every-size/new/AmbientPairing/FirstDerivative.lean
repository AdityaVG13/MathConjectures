import AmbientPairing.OneRow
import AmbientRestriction.ActualHessian

namespace AmbientPairing
open AmbientRestriction MvPolynomial
set_option backward.isDefEq.respectTransparency false
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Actual first derivative at the block-upper-triangular point. -/
theorem ambient_first_derivative (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ)
    (lam : n → ℂ) (W : Matrix n n ℂ) (a : n) :
    eval (fun _ => 0) (pderiv a (ambientPolynomial U v k lam W)) =
      linearCoefficient U v k * (W.updateRow a lam).permanent := by
  let D : Fin 3 ⊕ n → MvPolynomial n ℂ := Sum.elim (fun j => C (k j)) (fun _ => 0)
  have hd : pderiv a (ambientPolynomial U v k lam W) =
      ((ambientMatrix U v k lam W).updateRow (Sum.inr a) D).permanent := by
    apply SparseSeed.pderiv_permanent_row
    intro i j
    cases i with
    | inl i => cases j <;> simp [ambientMatrix]
    | inr i =>
      cases j <;> by_cases hi : i = a <;> simp [ambientMatrix, D, hi]
  rw [hd, SparseSeed.eval_permanent]
  have he : (fun i j => eval (fun _ => 0)
      (((ambientMatrix U v k lam W).updateRow (Sum.inr a) D) i j)) =
      addTop (leftTop U) (rightTop v lam) (bottomOne W k a) := by
    ext i j
    cases i with
    | inl i => cases j <;> simp [ambientMatrix, addTop, leftTop, rightTop]
    | inr i => cases j <;> by_cases hi : i = a <;>
        simp [Matrix.updateRow_apply, ambientMatrix, D, addTop, bottomOne, hi]
  rw [he, permanent_one_lower_row]

end AmbientPairing
#print axioms AmbientPairing.ambient_first_derivative
