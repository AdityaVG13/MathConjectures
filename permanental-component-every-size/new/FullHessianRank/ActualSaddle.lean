import FullHessianRank.SaddleRank
import AmbientHessianBlocks.NonLowerBlocks

set_option autoImplicit false
namespace ComponentFullHessianRank
noncomputable section
open Matrix ComponentChartJacobian ComponentAmbientHessian

abbrev Isotropic (k : ℕ) := Fin 4 ⊕ (Fin 2 × Fin k)
abbrev Remaining (k : ℕ) := Unit ⊕ LIndex k

def isotropicVariable (k : ℕ) : Isotropic k → Variables k
  | .inl c => bVar (ComponentUpperSeed.selected c)
  | .inr ij => vVar (ij.1.succ, ij.2)

def remainingVariable (k : ℕ) : Remaining k → Variables k
  | .inl _ => wVar (0, 0)
  | .inr ac => lVar ac

def normalVariable (k : ℕ) : Isotropic k ⊕ Remaining k → Variables k :=
  Sum.elim (isotropicVariable k) (remainingVariable k)

def actualCross (k : ℕ) : Matrix (Isotropic k) (Remaining k) ℂ :=
  fun i j => hessian k (isotropicVariable k i) (remainingVariable k j)

def actualResidual (k : ℕ) : Matrix (Remaining k) (Remaining k) ℂ :=
  fun i j => hessian k (remainingVariable k i) (remainingVariable k j)

theorem hessian_isotropic (k : ℕ) (i j : Isotropic k) :
    hessian k (isotropicVariable k i) (isotropicVariable k j) = 0 := by
  rcases i with i | i <;> rcases j with j | j
  · exact hessian_b_b k _ _
  · rw [hessian_symmetric]
    exact hessian_v_nonLower k _ _ (nonLower_b _)
  · exact hessian_v_nonLower k _ _ (nonLower_b _)
  · exact hessian_v_nonLower k _ _ (nonLower_v _)

/-- The matrix here is a literal submatrix of the genuine ambient Hessian.
No congruence model or surrogate Hessian is substituted. -/
theorem actual_normal_saddle (k : ℕ) :
    Matrix.submatrix (hessian k) (normalVariable k) (normalVariable k) =
      Matrix.fromBlocks 0 (actualCross k) (actualCross k).transpose (actualResidual k) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · exact hessian_isotropic k i j
  · rfl
  · exact hessian_symmetric k _ _
  · rfl

/-- Reduction of the desired full ambient lower bound to two precise
finite-dimensional cross/residual statements about actual Hessian entries. -/
theorem actual_rank_lower_bound (k : ℕ)
    (hA : Function.Injective (actualCross k).transpose.mulVec)
    (hQ : ∀ x : Remaining k → ℂ, (actualCross k).mulVec x = 0 →
      (∀ y : Remaining k → ℂ, (actualCross k).mulVec y = 0 →
        dotProduct y ((actualResidual k).mulVec x) = 0) → x = 0) :
    5 * (k + 1) + 3 ≤ Matrix.rank (hessian k) := by
  have hr := Matrix.rank_submatrix_le (hessian k) (normalVariable k) (normalVariable k)
  rw [actual_normal_saddle, saddle_rank _ _ hA hQ] at hr
  simp only [Isotropic, Remaining, LIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit] at hr
  omega

#print axioms actual_normal_saddle
#print axioms actual_rank_lower_bound
end
end ComponentFullHessianRank
