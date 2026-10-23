import SparseSeed.RowDerivative
import SparseSeed.TwoRowReplacement

namespace SparseSeed
open MvPolynomial

/-- The actual lower rank-one permanent polynomial from the ordinary argument. -/
noncomputable def lowerPolynomial (l : ℕ) : MvPolynomial (Option (Fin l)) ℂ :=
  rowPerturbationPolynomial (arrowhead l) (lambda l)

/-- Its actual Hessian at q=0, with no coefficient surrogates. -/
noncomputable def lowerHessian (l : ℕ) : Matrix (Option (Fin l)) (Option (Fin l)) ℂ :=
  fun a b => eval (fun _ => 0) (pderiv b (pderiv a (lowerPolynomial l)))

theorem lowerHessian_diagonal (l : ℕ) (a : Option (Fin l)) : lowerHessian l a a = 0 := by
  simp [lowerHessian, lowerPolynomial, pderiv_pderiv_self_rowPerturbation]

private theorem twoRows_eq_update (l : ℕ) (a b : Option (Fin l)) :
    twoRows l a b = ((arrowhead l).updateRow a (lambda l)).updateRow b (lambda l) := by
  ext i j
  by_cases hia : i = a <;> by_cases hib : i = b <;>
    simp_all [twoRows, Matrix.updateRow_apply]

theorem lowerHessian_eq_twoRows (l : ℕ) (a b : Option (Fin l)) (hab : a ≠ b) :
    lowerHessian l a b = (twoRows l a b).permanent := by
  unfold lowerHessian lowerPolynomial
  rw [eval_zero_pderiv_pderiv_rowPerturbation _ _ _ _ hab, twoRows_eq_update]

theorem lowerHessian_hub_leaf (l : ℕ) (a : Fin l) :
    lowerHessian l none (some a) = 8 * (l : ℂ) - 4 := by
  rw [lowerHessian_eq_twoRows _ _ _ (by simp), permanent_twoRows_hub_leaf]

theorem lowerHessian_distinct_leaves (l : ℕ) (a b : Fin l) (hab : a ≠ b) :
    lowerHessian l (some a) (some b) = 16 * (l : ℂ) - 40 := by
  rw [lowerHessian_eq_twoRows _ _ _ (by simpa using hab), permanent_twoRows_distinct_leaves _ _ _ hab]

theorem lowerHessian_symm (l : ℕ) (a b : Option (Fin l)) :
    lowerHessian l a b = lowerHessian l b a := by
  by_cases hab : a = b
  · subst b; rfl
  · rw [lowerHessian_eq_twoRows _ _ _ hab, lowerHessian_eq_twoRows _ _ _ (Ne.symm hab)]
    congr 1
    ext i j
    simp [twoRows, or_comm]

/-- Complete uniform formula for the actual lower-polynomial Hessian. -/
theorem lowerHessian_formula (l : ℕ) (a b : Option (Fin l)) :
    lowerHessian l a b = match a, b with
      | none, none => 0
      | none, some _ => 8 * (l : ℂ) - 4
      | some _, none => 8 * (l : ℂ) - 4
      | some i, some j => if i = j then 0 else 16 * (l : ℂ) - 40 := by
  cases a with
  | none =>
    cases b with
    | none => exact lowerHessian_diagonal l none
    | some b => exact lowerHessian_hub_leaf l b
  | some a =>
    cases b with
    | none => rw [lowerHessian_symm]; exact lowerHessian_hub_leaf l a
    | some b =>
      by_cases hab : a = b
      · subst b; simp [lowerHessian_diagonal]
      · simp [hab, lowerHessian_distinct_leaves l a b hab]

end SparseSeed

#print axioms SparseSeed.lowerHessian_formula
