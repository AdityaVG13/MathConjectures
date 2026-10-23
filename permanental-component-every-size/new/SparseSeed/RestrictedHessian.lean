import SparseSeed.LowerHessian
import SparseSeed.CofactorVector
import SparseSeed.LowerGradient
import UniformNormalKernel

namespace SparseSeed
open Finset

/-- Coordinates on the actual annihilator hyperplane `(P λ)ᵀq=0`. -/
noncomputable def kernelEmbedding (l : ℕ) : Matrix (Option (Fin l)) (Fin l) ℂ
  | none, _ => -(2 * (l : ℂ) - 3) / (2 * (l : ℂ) + 1)
  | some i, j => if i = j then 1 else 0

private theorem denom_ne_zero (l : ℕ) : 2 * (l : ℂ) + 1 ≠ 0 := by
  exact_mod_cast (show 2 * (l : ℤ) + 1 ≠ 0 by omega)

theorem kernelEmbedding_hub (l : ℕ) (q : Fin l → ℂ) :
    (kernelEmbedding l).mulVec q none =
      -(2 * (l : ℂ) - 3) / (2 * (l : ℂ) + 1) * ∑ i, q i := by
  simp [Matrix.mulVec, dotProduct, kernelEmbedding, Finset.mul_sum]

theorem kernelEmbedding_leaf (l : ℕ) (q : Fin l → ℂ) (i : Fin l) :
    (kernelEmbedding l).mulVec q (some i) = q i := by
  simp [Matrix.mulVec, dotProduct, kernelEmbedding]

theorem kernelEmbedding_injective (l : ℕ) : Function.Injective (kernelEmbedding l).mulVec := by
  intro q r h
  funext i
  have := congrArg (fun f => f (some i)) h
  simpa [kernelEmbedding_leaf] using this

/-- The coordinate map lands in the genuine cofactor-pairing hyperplane. -/
theorem kernelEmbedding_constraint (l : ℕ) (q : Fin l → ℂ) :
    dotProduct ((cofactorMatrix l).mulVec (lambda l)) ((kernelEmbedding l).mulVec q) = 0 := by
  rw [cofactor_lambda_pairing, kernelEmbedding_hub]
  simp_rw [kernelEmbedding_leaf]
  field_simp [denom_ne_zero]
  ring

private theorem hessian_mul_embedding_hub (l : ℕ) (j : Fin l) :
    (lowerHessian l * kernelEmbedding l) none j = 8 * (l : ℂ) - 4 := by
  simp [Matrix.mul_apply, Fintype.sum_option, kernelEmbedding, lowerHessian_formula, mul_ite]

private theorem hessian_mul_embedding_leaf (l : ℕ) (i j : Fin l) :
    (lowerHessian l * kernelEmbedding l) (some i) j =
      (8 * (l : ℂ) - 4) * (-(2 * (l : ℂ) - 3) / (2 * (l : ℂ) + 1)) +
      if i = j then 0 else 16 * (l : ℂ) - 40 := by
  simp [Matrix.mul_apply, Fintype.sum_option, kernelEmbedding, lowerHessian_formula, mul_ite]

/-- The actual Hessian, restricted to the actual annihilator hyperplane, is twice
`D I + C J`, with the coefficients required by the uniform normal calculation. -/
theorem restricted_lowerHessian_entry (l : ℕ) (i j : Fin l) :
    ((kernelEmbedding l).transpose * lowerHessian l * kernelEmbedding l) i j =
      2 * ((if i = j then -4 * (2 * (l : ℂ) - 5) else 0) - 32 / (2 * (l : ℂ) + 1)) := by
  rw [Matrix.mul_assoc]
  rw [Matrix.mul_apply, Fintype.sum_option]
  change kernelEmbedding l none i * (lowerHessian l * kernelEmbedding l) none j +
    (∑ t : Fin l, kernelEmbedding l (some t) i * (lowerHessian l * kernelEmbedding l) (some t) j) = _
  rw [hessian_mul_embedding_hub]
  simp only [kernelEmbedding]
  simp_rw [hessian_mul_embedding_leaf]
  simp only [ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hij : i = j
  · simp only [hij, ite_true]
    field_simp [denom_ne_zero]
    ring
  · simp only [hij, ite_false]
    field_simp [denom_ne_zero]
    ring

/-- Every vector in the actual cofactor-pairing hyperplane is represented by these coordinates. -/
theorem kernelEmbedding_exhaustive (l : ℕ) (q : Option (Fin l) → ℂ)
    (h : dotProduct ((cofactorMatrix l).mulVec (lambda l)) q = 0) :
    q = (kernelEmbedding l).mulVec (fun i => q (some i)) := by
  rw [cofactor_lambda_pairing] at h
  funext i
  cases i with
  | none =>
    rw [kernelEmbedding_hub]
    field_simp [denom_ne_zero]
    linear_combination h
  | some i => exact (kernelEmbedding_leaf l (fun j => q (some j)) i).symm

noncomputable def restrictedLowerHessian (l : ℕ) : Matrix (Fin l) (Fin l) ℂ :=
  (kernelEmbedding l).transpose * lowerHessian l * kernelEmbedding l

theorem restrictedLowerHessian_mulVec (l : ℕ) (q : Fin l → ℂ) (i : Fin l) :
    (restrictedLowerHessian l).mulVec q i =
      2 * (UniformBlockNormal.diagonal l * q i + UniformBlockNormal.common l * ∑ j, q j) := by
  unfold Matrix.mulVec dotProduct restrictedLowerHessian
  simp_rw [restricted_lowerHessian_entry]
  unfold UniformBlockNormal.diagonal UniformBlockNormal.common
  simp only [sub_eq_add_neg, add_mul, mul_add, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- Nonsingularity is now proved for the restriction of the actual permanent Hessian. -/
theorem restrictedLowerHessian_kernel_zero (l : ℕ) (q : Fin l → ℂ)
    (h : (restrictedLowerHessian l).mulVec q = 0) : q = 0 := by
  apply UniformBlockNormal.kernel_zero
  intro i
  have hi := congrFun h i
  rw [restrictedLowerHessian_mulVec] at hi
  exact (mul_eq_zero.mp hi).resolve_left (by norm_num)

theorem isUnit_restrictedLowerHessian (l : ℕ) : IsUnit (restrictedLowerHessian l) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro q r h
  have hz : (restrictedLowerHessian l).mulVec (q - r) = 0 := by
    rw [Matrix.mulVec_sub, h, sub_self]
  exact sub_eq_zero.mp (restrictedLowerHessian_kernel_zero l (q - r) hz)

theorem det_restrictedLowerHessian_ne_zero (l : ℕ) : (restrictedLowerHessian l).det ≠ 0 := by
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_restrictedLowerHessian l)).ne_zero

/-- The coordinate description is exactly the kernel of the genuine differential of G. -/
theorem lowerGradient_kernel_iff (l : ℕ) (q : Option (Fin l) → ℂ) :
    (∑ a, MvPolynomial.eval (fun _ => 0) (MvPolynomial.pderiv a (lowerPolynomial l)) * q a) = 0 ↔
      ∃ u : Fin l → ℂ, (kernelEmbedding l).mulVec u = q := by
  simp_rw [lowerGradient_eq_cofactor_mulVec]
  constructor
  · intro h
    exact ⟨(fun i => q (some i)), (kernelEmbedding_exhaustive l q h).symm⟩
  · rintro ⟨u, rfl⟩
    exact kernelEmbedding_constraint l u

end SparseSeed

#print axioms SparseSeed.kernelEmbedding_constraint
#print axioms SparseSeed.restricted_lowerHessian_entry

#print axioms SparseSeed.kernelEmbedding_exhaustive
#print axioms SparseSeed.restrictedLowerHessian_kernel_zero

#print axioms SparseSeed.isUnit_restrictedLowerHessian
#print axioms SparseSeed.det_restrictedLowerHessian_ne_zero

#print axioms SparseSeed.lowerGradient_kernel_iff
