import SparseSeed.CofactorDet
import SparseSeed.TwoRowReplacement

namespace SparseSeed
open Finset

/-- The exact coefficient of the hub coordinate in the linear term. -/
theorem cofactor_mulVec_lambda_hub (l : ℕ) :
    (cofactorMatrix l).mulVec (lambda l) none = 2 * (l : ℂ) + 1 := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_option, cofactorMatrix, cofactor_formula, lambda]
  ring

/-- The exact coefficient of every leaf coordinate in the linear term. -/
theorem cofactor_mulVec_lambda_leaf (l : ℕ) (a : Fin l) :
    (cofactorMatrix l).mulVec (lambda l) (some a) = 2 * (l : ℂ) - 3 := by
  unfold Matrix.mulVec dotProduct
  rw [Fintype.sum_option]
  have he (i : Fin l) : cofactorMatrix l (some a) (some i) * lambda l (some i) =
      2 + if i = a then (-4 : ℂ) else 0 := by
    by_cases hi : i = a
    · subst i; norm_num [cofactorMatrix, cofactor_formula, lambda]
    · simp [cofactorMatrix, cofactor_formula, lambda, hi, Ne.symm hi]
  simp_rw [he]
  simp [cofactorMatrix, cofactor_formula, lambda, Finset.sum_add_distrib]
  ring

/-- The genuine cofactor pairing has the asserted hyperplane equation. -/
theorem cofactor_lambda_pairing (l : ℕ) (q : Option (Fin l) → ℂ) :
    dotProduct ((cofactorMatrix l).mulVec (lambda l)) q =
      (2 * (l : ℂ) + 1) * q none + (2 * (l : ℂ) - 3) * ∑ i : Fin l, q (some i) := by
  unfold dotProduct
  rw [Fintype.sum_option, cofactor_mulVec_lambda_hub]
  simp_rw [cofactor_mulVec_lambda_leaf]
  rw [Finset.mul_sum]

end SparseSeed

#print axioms SparseSeed.cofactor_lambda_pairing
