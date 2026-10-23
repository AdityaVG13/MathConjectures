import AmbientRestriction.QuadraticFactor
import SparseSeed.RowDerivative

namespace AmbientRestriction
open Finset Equiv MvPolynomial
set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual block matrix [[U,vλᵀ],[qkᵀ,W]] over the polynomial ring in q. -/
noncomputable def ambientMatrix (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ)
    (lam : n → ℂ) (W : Matrix n n ℂ) : Matrix (Fin 3 ⊕ n) (Fin 3 ⊕ n) (MvPolynomial n ℂ)
  | Sum.inl i, Sum.inl j => C (U i j)
  | Sum.inl i, Sum.inr j => C (v i * lam j)
  | Sum.inr i, Sum.inl j => X i * C (k j)
  | Sum.inr i, Sum.inr j => C (W i j)

noncomputable def ambientPolynomial (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ)
    (lam : n → ℂ) (W : Matrix n n ℂ) : MvPolynomial n ℂ :=
  (ambientMatrix U v k lam W).permanent

private noncomputable def derivativeRow (k : Fin 3 → ℂ) : Fin 3 ⊕ n → MvPolynomial n ℂ
  | Sum.inl j => C (k j)
  | Sum.inr _ => 0

omit [Fintype n] in
private theorem derivative_entries (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ)
    (lam : n → ℂ) (W : Matrix n n ℂ) (a : n) (i j : Fin 3 ⊕ n) :
    pderiv a (ambientMatrix U v k lam W i j) =
      if i = Sum.inr a then derivativeRow k j else 0 := by
  cases i with
  | inl i => cases j <;> simp [ambientMatrix]
  | inr i =>
    cases j with
    | inl j =>
      by_cases hi : i = a
      · subst i; simp [ambientMatrix, derivativeRow]
      · simp [ambientMatrix, hi]
    | inr j => by_cases hi : i = a <;> simp [ambientMatrix, derivativeRow, hi]

private theorem first_derivative (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ)
    (lam : n → ℂ) (W : Matrix n n ℂ) (a : n) :
    pderiv a (ambientPolynomial U v k lam W) =
      ((ambientMatrix U v k lam W).updateRow (Sum.inr a) (derivativeRow k)).permanent := by
  apply SparseSeed.pderiv_permanent_row
  exact derivative_entries U v k lam W a

/-- The diagonal second derivatives vanish as actual polynomials. -/
theorem ambient_pderiv_self (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ)
    (lam : n → ℂ) (W : Matrix n n ℂ) (a : n) :
    pderiv a (pderiv a (ambientPolynomial U v k lam W)) = 0 := by
  rw [first_derivative]
  apply SparseSeed.pderiv_permanent_zero
  intro i j
  by_cases hi : i = Sum.inr a
  · subst i
    rw [Matrix.updateRow_self]
    cases j <;> simp [derivativeRow]
  · rw [Matrix.updateRow_ne hi, derivative_entries]
    simp [hi]

/-- The actual mixed derivative at zero is the genuinely row-replaced block permanent. -/
theorem ambient_mixed_derivative_replacement (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ)
    (lam : n → ℂ) (W : Matrix n n ℂ) (a b : n) (hab : a ≠ b) :
    eval (fun _ => 0) (pderiv b (pderiv a (ambientPolynomial U v k lam W))) =
      (addTop (leftTop U) (rightTop v lam) (bottomTwo W k a b)).permanent := by
  rw [first_derivative]
  rw [SparseSeed.pderiv_permanent_row b _ (Sum.inr b) (derivativeRow k)]
  · rw [SparseSeed.eval_permanent]
    congr 1
    ext i j
    cases i with
    | inl i => cases j <;>
        simp [Matrix.updateRow_apply, ambientMatrix, addTop, leftTop, rightTop]
    | inr i =>
      cases j <;> by_cases hia : i = a <;> by_cases hib : i = b <;>
        simp_all [Matrix.updateRow_apply, ambientMatrix, derivativeRow,
          addTop, bottomTwo]
  · intro i j
    by_cases hi : i = Sum.inr a
    · subst i
      rw [Matrix.updateRow_self]
      cases j <;> simp [derivativeRow, hab]
    · rw [Matrix.updateRow_ne hi, derivative_entries]

/-- The desired actual ambient lower-left Hessian identity, valid at arbitrary lower size
and for arbitrary upper/lower data. The factor 2η is proved, not assumed. -/
theorem ambient_hessian_eq (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ)
    (lam : n → ℂ) (W : Matrix n n ℂ) (a b : n) :
    eval (fun _ => 0) (pderiv b (pderiv a (ambientPolynomial U v k lam W))) =
      (2 * eta U v k) *
        eval (fun _ => 0) (pderiv b (pderiv a (SparseSeed.rowPerturbationPolynomial W lam))) := by
  by_cases hab : a = b
  · subst b
    rw [ambient_pderiv_self, SparseSeed.pderiv_pderiv_self_rowPerturbation]
    simp
  · rw [ambient_mixed_derivative_replacement U v k lam W a b hab,
      permanent_two_lower_rows U v k lam W a b hab,
      SparseSeed.eval_zero_pderiv_pderiv_rowPerturbation W lam a b hab]

/-- Evaluation confirms that this is the permanent of the stated block matrix, not a surrogate. -/
theorem eval_ambientPolynomial (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ)
    (lam : n → ℂ) (W : Matrix n n ℂ) (q : n → ℂ) :
    eval q (ambientPolynomial U v k lam W) =
      (Matrix.fromBlocks U (fun i j => v i * lam j) (fun i j => q i * k j) W).permanent := by
  unfold ambientPolynomial
  rw [SparseSeed.eval_permanent]
  congr 1
  ext i j
  cases i <;> cases j <;> simp [ambientMatrix, Matrix.fromBlocks]

end AmbientRestriction

#print axioms AmbientRestriction.ambient_mixed_derivative_replacement
#print axioms AmbientRestriction.ambient_hessian_eq
#print axioms AmbientRestriction.eval_ambientPolynomial
