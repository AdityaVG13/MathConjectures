import AmbientRestriction.ActualHessian
import SparseSeed.RestrictedHessian

namespace AmbientRestriction
open MvPolynomial

/-- The genuine lower-left rank-one block Hessian at the sparse lower seed. -/
noncomputable def ambientSeedHessian (l : ℕ) (U : Matrix (Fin 3) (Fin 3) ℂ)
    (v k : Fin 3 → ℂ) : Matrix (Option (Fin l)) (Option (Fin l)) ℂ :=
  fun a b => eval (fun _ => 0)
    (pderiv b (pderiv a (ambientPolynomial U v k (SparseSeed.lambda l) (SparseSeed.arrowhead l))))

theorem ambientSeedHessian_eq (l : ℕ) (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ) :
    ambientSeedHessian l U v k = (2 * eta U v k) • SparseSeed.lowerHessian l := by
  ext a b
  exact ambient_hessian_eq U v k (SparseSeed.lambda l) (SparseSeed.arrowhead l) a b

/-- Pull back the genuine ambient restriction to the genuine normal annihilator coordinates. -/
noncomputable def restrictedAmbientHessian (l : ℕ) (U : Matrix (Fin 3) (Fin 3) ℂ)
    (v k : Fin 3 → ℂ) : Matrix (Fin l) (Fin l) ℂ :=
  (SparseSeed.kernelEmbedding l).transpose * ambientSeedHessian l U v k * SparseSeed.kernelEmbedding l

theorem restrictedAmbientHessian_eq (l : ℕ) (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ) :
    restrictedAmbientHessian l U v k = (2 * eta U v k) • SparseSeed.restrictedLowerHessian l := by
  unfold restrictedAmbientHessian
  rw [ambientSeedHessian_eq, Matrix.mul_smul, Matrix.smul_mul]
  rfl

/-- The exact residual ambient Hessian is 4η(DI+CJ), including its scalar factor. -/
theorem restrictedAmbientHessian_entry (l : ℕ) (U : Matrix (Fin 3) (Fin 3) ℂ)
    (v k : Fin 3 → ℂ) (i j : Fin l) :
    restrictedAmbientHessian l U v k i j =
      (4 * eta U v k) *
        ((if i = j then -4 * (2 * (l : ℂ) - 5) else 0) - 32 / (2 * (l : ℂ) + 1)) := by
  rw [restrictedAmbientHessian_eq]
  change (2 * eta U v k) * SparseSeed.restrictedLowerHessian l i j = _
  unfold SparseSeed.restrictedLowerHessian
  rw [SparseSeed.restricted_lowerHessian_entry]
  ring

/-- For nonzero η the genuine residual ambient Hessian is nonsingular, uniformly in l. -/
theorem det_restrictedAmbientHessian_ne_zero (l : ℕ) (U : Matrix (Fin 3) (Fin 3) ℂ)
    (v k : Fin 3 → ℂ) (heta : eta U v k ≠ 0) :
    (restrictedAmbientHessian l U v k).det ≠ 0 := by
  rw [restrictedAmbientHessian_eq, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (by norm_num) heta))
    (SparseSeed.det_restrictedLowerHessian_ne_zero l)

theorem isUnit_restrictedAmbientHessian (l : ℕ) (U : Matrix (Fin 3) (Fin 3) ℂ)
    (v k : Fin 3 → ℂ) (heta : eta U v k ≠ 0) : IsUnit (restrictedAmbientHessian l U v k) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  exact isUnit_iff_ne_zero.mpr (det_restrictedAmbientHessian_ne_zero l U v k heta)

end AmbientRestriction

#print axioms AmbientRestriction.restrictedAmbientHessian_entry
#print axioms AmbientRestriction.det_restrictedAmbientHessian_ne_zero
#print axioms AmbientRestriction.isUnit_restrictedAmbientHessian
