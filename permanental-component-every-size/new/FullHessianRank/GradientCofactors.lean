import FullHessianRank.ActualLowerBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ComponentFullHessianRank
noncomputable section
open Matrix MvPolynomial ComponentChartJacobian ComponentAmbientHessian ComponentFamilyContainment

def finiteEntryEquiv (k : ℕ) : Variables k ≃ (Fin (3+k+1) × Fin (3+k+1)) :=
  (entryEquiv k).trans (Equiv.prodCongr (familyIndexEquiv k).symm (familyIndexEquiv k).symm)

def finiteAmbient (k : ℕ) : Matrix (Fin (3+k+1)) (Fin (3+k+1)) (P k) :=
  ambientFin (blockU k) (blockV k) (blockL k) (blockW k)

theorem finiteAmbient_entry (k : ℕ) (r c : Fin (3+k+1)) :
    finiteAmbient k r c = X ((finiteEntryEquiv k).symm (r,c)) := by
  change (Matrix.fromBlocks (blockU k) (blockV k) (blockL k) (blockW k))
    (familyIndexEquiv k r) (familyIndexEquiv k c) = _
  unfold blockU
  rw [← actualAmbient_blocks]
  rfl

theorem finiteAmbient_permanent (k : ℕ) : (finiteAmbient k).permanent = actualPolynomial k := by
  change (Matrix.submatrix (Matrix.fromBlocks (blockU k) (blockV k) (blockL k) (blockW k))
    (familyIndexEquiv k) (familyIndexEquiv k)).permanent = _
  unfold blockU
  rw [← actualAmbient_blocks, ComponentGeneralLaplace.permanent_reindex]
  rfl

/-- Actual grouped gradient equations are exactly the actual ambient finite
cofactors used by the scheme-theoretic containment theorem. -/
theorem actual_gradient_eq_cofactor (k : ℕ) (x : Variables k) :
    pderiv x (actualPolynomial k) =
      ((finiteAmbient k).submatrix ((finiteEntryEquiv k x).1.succAbove)
        ((finiteEntryEquiv k x).2.succAbove)).permanent := by
  rw [← finiteAmbient_permanent]
  convert ExceptionalCofactorDerivative.permanent_derivative_single x (finiteAmbient k)
    (finiteEntryEquiv k x).1 (finiteEntryEquiv k x).2 1 ?_ using 1
  · simp
  · intro r c
    rw [finiteAmbient_entry]
    have he : (finiteEntryEquiv k).symm (r,c) = x ↔
        r = (finiteEntryEquiv k x).1 ∧ c = (finiteEntryEquiv k x).2 := by
      rw [Equiv.symm_apply_eq]
      exact Prod.ext_iff
    simp only [pderiv_X, Pi.single_apply]
    simp [he]

#print axioms actual_gradient_eq_cofactor
end
end ComponentFullHessianRank
