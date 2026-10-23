import FullHessianRank.RankOneKernel
import AmbientPairing.FinKernelEmbedding
import AmbientHessianBlocks.UpperCrossKernel

set_option autoImplicit false
namespace ComponentFullHessianRank
noncomputable section
open Matrix ComponentChartJacobian ComponentAmbientHessian AmbientPairing

/-- Exact residual coordinates inside the selected remaining normal directions. -/
def remainingEmbedding (k : ℕ) : Matrix (Remaining k) (Fin k) ℂ
  | .inl _, _ => 0
  | .inr (a,c), j => kernelEmbeddingFin k a j * ComponentUpperSeed.k c

theorem remainingEmbedding_mulVec (k : ℕ) (u : Fin k → ℂ) :
    (remainingEmbedding k).mulVec u = rankOneRemaining k ((kernelEmbeddingFin k).mulVec u) := by
  ext i
  rcases i with i | ⟨a,c⟩
  · simp [Matrix.mulVec, dotProduct, remainingEmbedding, rankOneRemaining]
  · simp only [Matrix.mulVec, dotProduct, remainingEmbedding, rankOneRemaining, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem remainingEmbedding_in_kernel (k : ℕ) (u : Fin k → ℂ) :
    (actualCross k).mulVec ((remainingEmbedding k).mulVec u) = 0 := by
  rw [remainingEmbedding_mulVec]
  exact rankOneRemaining_in_kernel k _ (kernelEmbeddingFin_constraint k u)

theorem actual_annihilator_rank_one (k : ℕ) (x : Remaining k → ℂ)
    (hx : (actualCross k).mulVec x = 0) :
    ∃ q : Fin (k+1) → ℂ, x = rankOneRemaining k q ∧
      dotProduct ((finCofactorMatrix k).mulVec (seedLambda k)) q = 0 := by
  obtain ⟨hw, hc⟩ := actualCross_kernel_upper_constraints k x hx
  obtain ⟨q, hq, hcq⟩ := actual_annihilator_rank_one_of_weighted k x hx hc
  refine ⟨q, ?_, hcq⟩
  ext i
  rcases i with i | ⟨a,c⟩
  · cases i
    exact hw
  · exact hq a c

theorem remainingEmbedding_exhaustive (k : ℕ) (x : Remaining k → ℂ)
    (hx : (actualCross k).mulVec x = 0) :
    ∃ u : Fin k → ℂ, (remainingEmbedding k).mulVec u = x := by
  obtain ⟨q, rfl, hq⟩ := actual_annihilator_rank_one k x hx
  refine ⟨fun i => q i.succ, ?_⟩
  rw [remainingEmbedding_mulVec, ← kernelEmbeddingFin_exhaustive k q hq]

#print axioms actual_annihilator_rank_one
#print axioms remainingEmbedding_exhaustive
end
end ComponentFullHessianRank
