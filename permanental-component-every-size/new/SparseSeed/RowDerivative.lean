import SparseSeed.Arrowhead
import Mathlib.Algebra.MvPolynomial.PDeriv

set_option backward.isDefEq.respectTransparency false

namespace SparseSeed
open Finset Equiv MvPolynomial

/-- If dependence on a variable is confined to one row, differentiation replaces that row
by its derivative. This is an identity of actual multivariate polynomials. -/
theorem pderiv_permanent_row {n v : Type*} [DecidableEq n] [Fintype n] [DecidableEq v]
    (x : v) (M : Matrix n n (MvPolynomial v ℂ)) (a : n) (D : n → MvPolynomial v ℂ)
    (h : ∀ i j, pderiv x (M i j) = if i = a then D j else 0) :
    pderiv x M.permanent = (M.updateRow a D).permanent := by
  unfold Matrix.permanent
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  let j := σ.symm a
  have hj : σ j = a := σ.apply_symm_apply a
  have hother (i : n) (hi : i ∈ (Finset.univ : Finset n).erase j) : σ i ≠ a := by
    intro hia
    exact (Finset.mem_erase.mp hi).1 (σ.injective (hia.trans hj.symm))
  have hrest : pderiv x (∏ i ∈ (Finset.univ : Finset n).erase j, M (σ i) i) = 0 := by
    apply Finset.prod_induction _ (fun f => pderiv x f = 0)
    · intro f g hf hg
      rw [pderiv_mul, hf, hg, zero_mul, mul_zero, add_zero]
    · exact Derivation.map_one_eq_zero _
    · intro i hi
      simp [h, hother i hi]
  have hupdated : (∏ i, M.updateRow a D (σ i) i) =
      D j * ∏ i ∈ (Finset.univ : Finset n).erase j, M (σ i) i := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    rw [hj, Matrix.updateRow_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Matrix.updateRow_ne (hother i hi)]
  rw [hupdated, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), pderiv_mul, hrest]
  simp [h, hj]

/-- The actual permanent polynomial of a row-parameterized rank-one perturbation. -/
noncomputable def rowPerturbationPolynomial {n : Type*} [DecidableEq n] [Fintype n]
    (A : Matrix n n ℂ) (v : n → ℂ) : MvPolynomial n ℂ :=
  Matrix.permanent (fun i j => C (A i j) + X i * C (v j) : Matrix n n (MvPolynomial n ℂ))

/-- Evaluation commutes with the permanent sum. -/
theorem eval_permanent {n v : Type*} [DecidableEq n] [Fintype n]
    (q : v → ℂ) (M : Matrix n n (MvPolynomial v ℂ)) :
    eval q M.permanent = Matrix.permanent (fun i j => eval q (M i j) : Matrix n n ℂ) := by
  simp [Matrix.permanent, map_sum, map_prod]

/-- The derivative of the actual rank-one perturbation permanent, evaluated at zero,
is the permanent with the corresponding row replaced by the perturbing vector. -/
theorem eval_zero_pderiv_rowPerturbation {n : Type*} [DecidableEq n] [Fintype n]
    (A : Matrix n n ℂ) (v : n → ℂ) (a : n) :
    eval (fun _ => 0) (pderiv a (rowPerturbationPolynomial A v)) =
      (A.updateRow a v).permanent := by
  unfold rowPerturbationPolynomial
  rw [pderiv_permanent_row a _ a (fun j => C (v j))]
  · rw [eval_permanent]
    congr 1
    ext i j
    by_cases hi : i = a <;> simp [Matrix.updateRow_apply, hi]
  · intro i j
    by_cases hi : i = a
    · subst i; simp
    · simp [hi]

/-- Distinct mixed second derivatives of the actual rank-one perturbation permanent,
evaluated at zero, are exactly the two-row replacement permanents. -/
theorem eval_zero_pderiv_pderiv_rowPerturbation {n : Type*} [DecidableEq n] [Fintype n]
    (A : Matrix n n ℂ) (v : n → ℂ) (a b : n) (hab : a ≠ b) :
    eval (fun _ => 0) (pderiv b (pderiv a (rowPerturbationPolynomial A v))) =
      ((A.updateRow a v).updateRow b v).permanent := by
  unfold rowPerturbationPolynomial
  rw [pderiv_permanent_row a _ a (fun j => C (v j))]
  · rw [pderiv_permanent_row b _ b (fun j => C (v j))]
    · rw [eval_permanent]
      congr 1
      ext i j
      by_cases hia : i = a <;> by_cases hib : i = b <;>
        simp_all [Matrix.updateRow_apply]
    · intro i j
      by_cases hia : i = a
      · subst i; simp [Matrix.updateRow_self, hab]
      · rw [Matrix.updateRow_ne hia]
        by_cases hib : i = b
        · subst i; simp
        · simp [hib]
  · intro i j
    by_cases hi : i = a
    · subst i; simp
    · simp [hi]

/-- A matrix independent of a variable has permanent independent of that variable. -/
theorem pderiv_permanent_zero {n v : Type*} [DecidableEq n] [Fintype n] [DecidableEq v]
    (x : v) (M : Matrix n n (MvPolynomial v ℂ))
    (h : ∀ i j, pderiv x (M i j) = 0) : pderiv x M.permanent = 0 := by
  rw [Matrix.permanent, map_sum]
  apply Finset.sum_eq_zero
  intro σ _
  apply Finset.prod_induction _ (fun f => pderiv x f = 0)
  · intro f g hf hg
    rw [pderiv_mul, hf, hg, zero_mul, mul_zero, add_zero]
  · exact Derivation.map_one_eq_zero _
  · intro i _
    exact h (σ i) i

/-- Diagonal second derivatives vanish as polynomials, not merely at the seed. -/
theorem pderiv_pderiv_self_rowPerturbation {n : Type*} [DecidableEq n] [Fintype n]
    (A : Matrix n n ℂ) (v : n → ℂ) (a : n) :
    pderiv a (pderiv a (rowPerturbationPolynomial A v)) = 0 := by
  unfold rowPerturbationPolynomial
  rw [pderiv_permanent_row a _ a (fun j => C (v j))]
  · apply pderiv_permanent_zero
    intro i j
    by_cases hi : i = a
    · subst i; simp [Matrix.updateRow_self]
    · rw [Matrix.updateRow_ne hi]
      simp [hi]
  · intro i j
    by_cases hi : i = a
    · subst i; simp
    · simp [hi]

/-- The polynomial really evaluates to the indicated rank-one perturbation permanent. -/
theorem eval_rowPerturbationPolynomial {n : Type*} [DecidableEq n] [Fintype n]
    (A : Matrix n n ℂ) (v q : n → ℂ) :
    eval q (rowPerturbationPolynomial A v) =
      Matrix.permanent (fun i j => A i j + q i * v j) := by
  unfold rowPerturbationPolynomial
  rw [eval_permanent]
  congr 1
  ext i j
  simp

end SparseSeed

#print axioms SparseSeed.pderiv_permanent_row
#print axioms SparseSeed.eval_zero_pderiv_rowPerturbation
#print axioms SparseSeed.eval_zero_pderiv_pderiv_rowPerturbation

#print axioms SparseSeed.pderiv_pderiv_self_rowPerturbation
#print axioms SparseSeed.eval_rowPerturbationPolynomial
