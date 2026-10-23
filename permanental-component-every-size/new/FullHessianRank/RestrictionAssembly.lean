import FullHessianRank.RemainingEmbedding
import FullHessianRank.ResidualCriterion
import AmbientPairing.FinAmbientHessian
import AmbientPairing.FinKernelEmbedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ComponentFullHessianRank
noncomputable section
open Matrix ComponentChartJacobian ComponentAmbientHessian AmbientPairing

/-- Rank-one lower-left directions, before imposing the single cofactor constraint. -/
def lowerRankOneEmbedding (k : ℕ) : Matrix (Remaining k) (Fin (k+1)) ℂ
  | .inl _, _ => 0
  | .inr (a,c), b => if a = b then ComponentUpperSeed.k c else 0

def contractedLowerHessian (k : ℕ) : Matrix (Fin (k+1)) (Fin (k+1)) ℂ :=
  fun a b => ∑ c : Fin 3, ∑ d : Fin 3,
    ComponentUpperSeed.k c * ComponentUpperSeed.k d * hessian k (lVar (a,c)) (lVar (b,d))

theorem lowerRankOne_congruence (k : ℕ) :
    (lowerRankOneEmbedding k).transpose * actualResidual k * lowerRankOneEmbedding k =
      contractedLowerHessian k := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type,
    Fintype.sum_unique, Fintype.sum_prod_type, lowerRankOneEmbedding, mul_zero,
    zero_mul, Finset.sum_const_zero, add_zero, zero_add, ite_mul, mul_ite]
  simp only [actualResidual, remainingVariable]
  simp only [← Finset.ite_sum_zero, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [contractedLowerHessian, actualResidual, remainingVariable]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem remainingEmbedding_factor (k : ℕ) :
    remainingEmbedding k = lowerRankOneEmbedding k * kernelEmbeddingFin k := by
  ext i j
  rcases i with i | ⟨a,c⟩
  · simp [remainingEmbedding, lowerRankOneEmbedding, Matrix.mul_apply]
  · simp [remainingEmbedding, lowerRankOneEmbedding, Matrix.mul_apply, mul_comm]

theorem remaining_congruence (k : ℕ) :
    (remainingEmbedding k).transpose * actualResidual k * remainingEmbedding k =
      (kernelEmbeddingFin k).transpose * contractedLowerHessian k * kernelEmbeddingFin k := by
  rw [remainingEmbedding_factor]
  calc
    _ = (kernelEmbeddingFin k).transpose *
        ((lowerRankOneEmbedding k).transpose * actualResidual k * lowerRankOneEmbedding k) *
        kernelEmbeddingFin k := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = _ := by rw [lowerRankOne_congruence]

/-- All actual normal blocks and annihilator coordinate assembly are discharged.
The only input here is the precise chain-rule identity for the shared Hessian. -/
theorem actual_rank_lower_bound_of_chain_rule (k : ℕ)
    (hchain : contractedLowerHessian k =
      finAmbientHessian k ComponentUpperSeed.U ComponentUpperSeed.v ComponentUpperSeed.k) :
    5 * (k + 1) + 3 ≤ Matrix.rank (hessian k) := by
  apply actual_rank_lower_bound k (actualCross_transpose_injective k)
  apply residual_kernel_zero (actualCross k) (actualResidual k) (remainingEmbedding k)
    (remainingEmbedding_in_kernel k) (remainingEmbedding_exhaustive k)
  rw [remaining_congruence, hchain, ambient_fin_restricted]
  apply AmbientRestriction.isUnit_restrictedAmbientHessian
  exact ComponentUpperSeed.eta_ne_zero

#print axioms lowerRankOne_congruence
#print axioms actual_rank_lower_bound_of_chain_rule
end
end ComponentFullHessianRank
