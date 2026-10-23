import FullHessianRank.RestrictionAssembly

set_option autoImplicit false
namespace ComponentFullHessianRank
noncomputable section
open Matrix ComponentChartJacobian ComponentAmbientHessian AmbientPairing

def normalGeneratorEquiv (k : ℕ) : Isotropic k ⊕ Remaining k ≃ Generators k where
  toFun
    | .inl (.inl c) => .inl c
    | .inl (.inr ij) => .inr (.inr (.inr ij))
    | .inr (.inl u) => .inr (.inl u)
    | .inr (.inr ac) => .inr (.inr (.inl ac))
  invFun
    | .inl c => .inl (.inl c)
    | .inr (.inl u) => .inr (.inl u)
    | .inr (.inr (.inl ac)) => .inr (.inr ac)
    | .inr (.inr (.inr ij)) => .inl (.inr ij)
  left_inv x := by rcases x with (c | ij) | (u | ac) <;> rfl
  right_inv x := by rcases x with c | (u | (ac | ij)) <;> rfl

theorem normalVariable_eq (k : ℕ) (i : Isotropic k ⊕ Remaining k) :
    normalVariable k i = selected k (normalGeneratorEquiv k i) := by
  rcases i with (c | ij) | (u | ac) <;> rfl

theorem actual_normal_isUnit_of_chain_rule (k : ℕ)
    (hchain : contractedLowerHessian k =
      finAmbientHessian k ComponentUpperSeed.U ComponentUpperSeed.v ComponentUpperSeed.k) :
    IsUnit (Matrix.submatrix (hessian k) (normalVariable k) (normalVariable k)) := by
  rw [actual_normal_saddle]
  apply saddle_isUnit _ _ (actualCross_transpose_injective k)
  apply residual_kernel_zero (actualCross k) (actualResidual k) (remainingEmbedding k)
    (remainingEmbedding_in_kernel k) (remainingEmbedding_exhaustive k)
  rw [remaining_congruence, hchain, ambient_fin_restricted]
  exact AmbientRestriction.isUnit_restrictedAmbientHessian _ _ _ _ ComponentUpperSeed.eta_ne_zero

/-- The originally selected normal minor is nonsingular, not just an unrelated
matrix with the same size, conditional only on the exact chain-rule bridge. -/
theorem actual_selected_isUnit_of_chain_rule (k : ℕ)
    (hchain : contractedLowerHessian k =
      finAmbientHessian k ComponentUpperSeed.U ComponentUpperSeed.v ComponentUpperSeed.k) :
    IsUnit (Matrix.submatrix (hessian k) (selected k) (selected k)) := by
  have hh := actual_normal_isUnit_of_chain_rule k hchain
  have he : Matrix.submatrix (hessian k) (normalVariable k) (normalVariable k) =
      (Matrix.submatrix (hessian k) (selected k) (selected k)).submatrix
        (normalGeneratorEquiv k) (normalGeneratorEquiv k) := by
    ext i j
    change hessian k (normalVariable k i) (normalVariable k j) =
      hessian k (selected k (normalGeneratorEquiv k i)) (selected k (normalGeneratorEquiv k j))
    rw [normalVariable_eq, normalVariable_eq]
  rw [he] at hh
  exact (Matrix.isUnit_submatrix_equiv (normalGeneratorEquiv k) (normalGeneratorEquiv k)).mp hh

#print axioms actual_selected_isUnit_of_chain_rule
end
end ComponentFullHessianRank
