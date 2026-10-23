import SparseSeed.LowerHessian
import SparseSeed.CofactorVector

namespace SparseSeed
open Finset Equiv MvPolynomial

/-- General unsigned row expansion, in the same deletion convention as the computed cofactors. -/
theorem permanent_option_row {n : Type*} [DecidableEq n] [Fintype n]
    (M : Matrix (Option n) (Option n) ℂ) (a : Option n) :
    M.permanent = ∑ b : Option n, M a b *
      (M.submatrix (fun i => swap none a (some i)) (fun j => swap none b (some j))).permanent := by
  rw [← Matrix.permanent_permute_cols (swap none a) M,
    ← Matrix.permanent_transpose, permanent_option_hub_column]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Matrix.submatrix_apply, Matrix.transpose_apply, Equiv.swap_apply_left, id_eq]
  congr 1
  rw [← Matrix.permanent_transpose]
  rfl

/-- The actual first derivatives of G at zero are exactly the previously computed Pλ vector. -/
theorem lowerGradient_eq_cofactor_mulVec (l : ℕ) (a : Option (Fin l)) :
    eval (fun _ => 0) (pderiv a (lowerPolynomial l)) =
      (cofactorMatrix l).mulVec (lambda l) a := by
  unfold lowerPolynomial
  rw [eval_zero_pderiv_rowPerturbation, permanent_option_row]
  unfold Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro b _
  rw [Matrix.updateRow_self]
  have hrow (i : Fin l) : swap none a (some i) ≠ a := by
    intro hi
    have hn : swap none a none = a := Equiv.swap_apply_left _ _
    have := (swap none a).injective (hi.trans hn.symm)
    cases this
  have hminor : ((arrowhead l).updateRow a (lambda l)).submatrix
      (fun i => swap none a (some i)) (fun j => swap none b (some j)) =
      (arrowhead l).submatrix (fun i => swap none a (some i)) (fun j => swap none b (some j)) := by
    ext i j
    simp [Matrix.submatrix, Matrix.updateRow_ne (hrow i)]
  rw [hminor]
  exact mul_comm _ _

/-- The exact tangent constraint for G is the actual cofactor-pairing hyperplane. -/
theorem lowerGradient_pairing (l : ℕ) (q : Option (Fin l) → ℂ) :
    (∑ a, eval (fun _ => 0) (pderiv a (lowerPolynomial l)) * q a) =
      (2 * (l : ℂ) + 1) * q none + (2 * (l : ℂ) - 3) * ∑ i : Fin l, q (some i) := by
  simp_rw [lowerGradient_eq_cofactor_mulVec]
  exact cofactor_lambda_pairing l q

end SparseSeed

#print axioms SparseSeed.permanent_option_row
#print axioms SparseSeed.lowerGradient_eq_cofactor_mulVec
#print axioms SparseSeed.lowerGradient_pairing
