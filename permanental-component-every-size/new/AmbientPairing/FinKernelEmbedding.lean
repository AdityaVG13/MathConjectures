import AmbientPairing.LowerCofactor
import AmbientRestriction.RestrictedAmbient

namespace AmbientPairing
open Matrix Finset
set_option backward.isDefEq.respectTransparency false
noncomputable section

def kernelEmbeddingFin (k : ℕ) : Matrix (Fin (k+1)) (Fin k) ℂ :=
  (SparseSeed.kernelEmbedding k).submatrix (finSuccEquiv k) id

theorem kernelEmbeddingFin_mulVec (k : ℕ) (u : Fin k → ℂ) (a : Fin (k+1)) :
    (kernelEmbeddingFin k).mulVec u a =
      (SparseSeed.kernelEmbedding k).mulVec u (finSuccEquiv k a) := rfl

theorem fin_constraint_transport (k : ℕ) (q : Fin (k+1) → ℂ) :
    dotProduct ((finCofactorMatrix k).mulVec (seedLambda k)) q =
      dotProduct ((SparseSeed.cofactorMatrix k).mulVec (SparseSeed.lambda k))
        (fun a => q ((finSuccEquiv k).symm a)) := by
  unfold dotProduct
  apply Fintype.sum_equiv (finSuccEquiv k)
  intro a
  rw [finCofactor_mul_lambda]
  simp

theorem kernelEmbeddingFin_constraint (k : ℕ) (u : Fin k → ℂ) :
    dotProduct ((finCofactorMatrix k).mulVec (seedLambda k)) ((kernelEmbeddingFin k).mulVec u) = 0 := by
  rw [fin_constraint_transport]
  have he : (fun a => (kernelEmbeddingFin k).mulVec u ((finSuccEquiv k).symm a)) =
      (SparseSeed.kernelEmbedding k).mulVec u := by
    funext a
    rw [kernelEmbeddingFin_mulVec]
    simp
  rw [he]
  exact SparseSeed.kernelEmbedding_constraint k u

theorem kernelEmbeddingFin_exhaustive (k : ℕ) (q : Fin (k+1) → ℂ)
    (hq : dotProduct ((finCofactorMatrix k).mulVec (seedLambda k)) q = 0) :
    q = (kernelEmbeddingFin k).mulVec (fun i => q i.succ) := by
  rw [fin_constraint_transport] at hq
  have he := SparseSeed.kernelEmbedding_exhaustive k (fun a => q ((finSuccEquiv k).symm a)) hq
  funext a
  have hh := congrFun he (finSuccEquiv k a)
  simpa [kernelEmbeddingFin_mulVec] using hh

theorem kernelEmbeddingFin_injective (k : ℕ) : Function.Injective (kernelEmbeddingFin k).mulVec := by
  intro u v h
  apply SparseSeed.kernelEmbedding_injective k
  funext a
  have hh := congrFun h ((finSuccEquiv k).symm a)
  simpa [kernelEmbeddingFin_mulVec] using hh

/-- Reindexing both the Hessian and embedding leaves the restricted matrix unchanged. -/
theorem restricted_matrix_reindex (k : ℕ) (H : Matrix (Option (Fin k)) (Option (Fin k)) ℂ) :
    (kernelEmbeddingFin k).transpose * H.submatrix (finSuccEquiv k) (finSuccEquiv k) *
      kernelEmbeddingFin k =
        (SparseSeed.kernelEmbedding k).transpose * H * SparseSeed.kernelEmbedding k := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, kernelEmbeddingFin, Matrix.submatrix_apply]
  apply Fintype.sum_equiv (finSuccEquiv k)
  intro a
  congr 1
  apply Fintype.sum_equiv (finSuccEquiv k)
  intro b
  rfl

theorem restricted_ambient_reindex (k : ℕ) (U : Matrix (Fin 3) (Fin 3) ℂ) (v w : Fin 3 → ℂ) :
    (kernelEmbeddingFin k).transpose *
      (AmbientRestriction.ambientSeedHessian k U v w).submatrix (finSuccEquiv k) (finSuccEquiv k) *
      kernelEmbeddingFin k = AmbientRestriction.restrictedAmbientHessian k U v w := by
  exact restricted_matrix_reindex k _

end
end AmbientPairing
#print axioms AmbientPairing.kernelEmbeddingFin_exhaustive
#print axioms AmbientPairing.kernelEmbeddingFin_constraint
#print axioms AmbientPairing.restricted_ambient_reindex
