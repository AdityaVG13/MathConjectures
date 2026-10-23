import AmbientPairing.FinKernelEmbedding
import GeneralLaplace.GeneralLaplace

namespace AmbientPairing
open MvPolynomial Matrix
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- The lower row-perturbation Hessian is unchanged by the explicit finite-index relabeling. -/
theorem lower_hessian_fin_reindex (k : ℕ) (a b : Fin (k+1)) :
    eval (fun _ => 0) (pderiv b (pderiv a
      (SparseSeed.rowPerturbationPolynomial (SparseSeed.finArrowhead k) (seedLambda k)))) =
      SparseSeed.lowerHessian k (finSuccEquiv k a) (finSuccEquiv k b) := by
  by_cases hab : a = b
  · subst b
    rw [SparseSeed.pderiv_pderiv_self_rowPerturbation]
    simp [SparseSeed.lowerHessian_diagonal]
  · rw [SparseSeed.eval_zero_pderiv_pderiv_rowPerturbation _ _ _ _ hab]
    change _ = eval (fun _ => 0) (pderiv (finSuccEquiv k b) (pderiv (finSuccEquiv k a)
      (SparseSeed.rowPerturbationPolynomial (SparseSeed.arrowhead k) (SparseSeed.lambda k))))
    rw [SparseSeed.eval_zero_pderiv_pderiv_rowPerturbation _ _ _ _
      ((finSuccEquiv k).injective.ne hab)]
    rw [← ComponentGeneralLaplace.permanent_reindex (finSuccEquiv k)]
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.updateRow_apply]
    have hai : finSuccEquiv k i = finSuccEquiv k a ↔ i = a := (finSuccEquiv k).injective.eq_iff
    have hbi : finSuccEquiv k i = finSuccEquiv k b ↔ i = b := (finSuccEquiv k).injective.eq_iff
    simp only [hai, hbi]
    by_cases hi : i = a <;> by_cases hj : i = b <;>
      simp [hi, hj, seedLambda_reindex, SparseSeed.finArrowhead, Matrix.submatrix]

/-- The actual Fin-indexed ambient restriction Hessian is the reindexed accepted one. -/
theorem ambient_hessian_fin_reindex (k : ℕ) (U : Matrix (Fin 3) (Fin 3) ℂ)
    (v w : Fin 3 → ℂ) (a b : Fin (k+1)) :
    eval (fun _ => 0) (pderiv b (pderiv a
      (AmbientRestriction.ambientPolynomial U v w (seedLambda k) (SparseSeed.finArrowhead k)))) =
      AmbientRestriction.ambientSeedHessian k U v w (finSuccEquiv k a) (finSuccEquiv k b) := by
  rw [AmbientRestriction.ambient_hessian_eq, lower_hessian_fin_reindex,
    AmbientRestriction.ambientSeedHessian_eq]
  rfl

def finAmbientHessian (k : ℕ) (U : Matrix (Fin 3) (Fin 3) ℂ) (v w : Fin 3 → ℂ) :
    Matrix (Fin (k+1)) (Fin (k+1)) ℂ := fun a b =>
  eval (fun _ => 0) (pderiv b (pderiv a
    (AmbientRestriction.ambientPolynomial U v w (seedLambda k) (SparseSeed.finArrowhead k))))

/-- Pulling the genuine Fin ambient restriction back along EFin gives the accepted residual matrix. -/
theorem ambient_fin_restricted (k : ℕ) (U : Matrix (Fin 3) (Fin 3) ℂ) (v w : Fin 3 → ℂ) :
    (kernelEmbeddingFin k).transpose * finAmbientHessian k U v w *
      kernelEmbeddingFin k = AmbientRestriction.restrictedAmbientHessian k U v w := by
  have he : finAmbientHessian k U v w =
      (AmbientRestriction.ambientSeedHessian k U v w).submatrix (finSuccEquiv k) (finSuccEquiv k) := by
    ext a b
    exact ambient_hessian_fin_reindex k U v w a b
  rw [he, restricted_ambient_reindex]

end
end AmbientPairing
#print axioms AmbientPairing.ambient_hessian_fin_reindex
#print axioms AmbientPairing.ambient_fin_restricted
