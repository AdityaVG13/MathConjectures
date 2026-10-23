import FullHessianRank.ActualSaddle
import FullHessianRank.AnnihilatorRows
import AmbientPairing.LowerCofactor

set_option autoImplicit false
namespace ComponentFullHessianRank
noncomputable section
open Matrix ComponentChartJacobian ComponentAmbientHessian AmbientPairing

/-- The lower-left matrix encoded by the remaining normal coordinates. -/
def lowerCoordinates (k : ℕ) (x : Remaining k → ℂ) : Matrix (Fin (k+1)) (Fin 3) ℂ :=
  fun a c => x (.inr (a,c))

theorem actual_cross_right (k : ℕ) (x : Remaining k → ℂ) (i : Fin 2) (j : Fin k) :
    (actualCross k).mulVec x (.inr (i,j)) =
      ∑ c : Fin 3, ComponentUpperSeed.T c i.succ *
        ((finCofactorMatrix k).transpose * lowerCoordinates k x) j.succ c := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_unique]
  have hz : actualCross k (.inr (i,j)) (.inl ()) = 0 :=
    hessian_v_nonLower k _ _ (nonLower_w _)
  rw [hz, zero_mul, zero_add]
  simp only [Fintype.sum_prod_type]
  have he (a : Fin (k+1)) (c : Fin 3) :
      actualCross k (.inr (i,j)) (.inr (a,c)) =
        ComponentUpperSeed.T c i.succ * finCofactorMatrix k a j.succ := by
    change hessian k (selected k (.inr (.inr (.inr (i,j))))) (lVar (a,c)) = _
    rw [hessian_symmetric, hessian_left_selected_right]
  simp only [he, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, lowerCoordinates]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem weighted_transpose_lower (k : ℕ) (x : Remaining k → ℂ) (c : Fin 3) :
    (∑ j, seedLambda k j * ((finCofactorMatrix k).transpose * lowerCoordinates k x) j c) =
      ∑ a, (finCofactorMatrix k).mulVec (seedLambda k) a * x (.inr (a,c)) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum, Finset.sum_mul, lowerCoordinates]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem actual_annihilator_rank_one_of_weighted (k : ℕ) (x : Remaining k → ℂ)
    (hx : (actualCross k).mulVec x = 0)
    (hc : ∀ c : Fin 3, ∑ a, (finCofactorMatrix k).mulVec (seedLambda k) a * x (.inr (a,c)) = 0) :
    ∃ q : Fin (k+1) → ℂ,
      (∀ a c, x (.inr (a,c)) = q a * ComponentUpperSeed.k c) ∧
      dotProduct ((finCofactorMatrix k).mulVec (seedLambda k)) q = 0 := by
  apply annihilator_rank_one k (finCofactorMatrix k)
    (isUnit_iff_ne_zero.mpr (det_finCofactorMatrix_ne_zero k)) (seedLambda k) (by rfl)
    (lowerCoordinates k x)
  · intro j i
    rw [← actual_cross_right]
    exact congrFun hx (.inr (i,j))
  · intro c
    rw [weighted_transpose_lower]
    exact hc c

#print axioms actual_annihilator_rank_one_of_weighted
end
end ComponentFullHessianRank
