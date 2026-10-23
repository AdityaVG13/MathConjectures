import FullHessianRank.ActualAnnihilator
import AmbientPairing.CrossInjective

set_option autoImplicit false
namespace ComponentFullHessianRank
noncomputable section
open Matrix ComponentChartJacobian ComponentAmbientHessian AmbientPairing

def rankOneRemaining (k : ℕ) (q : Fin (k+1) → ℂ) : Remaining k → ℂ
  | .inl _ => 0
  | .inr (a,c) => q a * ComponentUpperSeed.k c

@[simp] theorem rankOneRemaining_zero (k : ℕ) : rankOneRemaining k 0 = 0 := by
  ext i
  rcases i with i | ⟨a,c⟩ <;> simp [rankOneRemaining]

theorem rankOneRemaining_in_kernel (k : ℕ) (q : Fin (k+1) → ℂ)
    (hq : dotProduct ((finCofactorMatrix k).mulVec (seedLambda k)) q = 0) :
    (actualCross k).mulVec (rankOneRemaining k q) = 0 := by
  ext i
  rcases i with s | ⟨i,j⟩
  · simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_unique,
      rankOneRemaining, mul_zero, zero_add, Fintype.sum_prod_type, actualCross_upper_left]
    rw [Finset.sum_comm]
    have he (c : Fin 3) :
        (∑ a, ComponentUpperSeed.jac c.castSucc s * (finCofactorMatrix k).mulVec (seedLambda k) a *
          (q a * ComponentUpperSeed.k c)) =
        (ComponentUpperSeed.jac c.castSucc s * ComponentUpperSeed.k c) *
          dotProduct ((finCofactorMatrix k).mulVec (seedLambda k)) q := by
      simp only [dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    change (∑ c : Fin 3, ∑ a : Fin (k+1), ComponentUpperSeed.jac c.castSucc s * (finCofactorMatrix k).mulVec (seedLambda k) a * (q a * ComponentUpperSeed.k c)) = 0
    simp only [he, hq, mul_zero, Finset.sum_const_zero]
  · simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_unique,
      rankOneRemaining, mul_zero, zero_add, Fintype.sum_prod_type, actualCross_right_left]
    have he (a : Fin (k+1)) :
        (∑ c, ComponentUpperSeed.T c i.succ * finCofactorMatrix k a j.succ *
          (q a * ComponentUpperSeed.k c)) =
        (finCofactorMatrix k a j.succ * q a) *
          (ComponentUpperSeed.T.transpose.mulVec ComponentUpperSeed.k) i.succ := by
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    simp only [he, ComponentUpperSeed.left_kernel, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

#print axioms rankOneRemaining_in_kernel
end
end ComponentFullHessianRank
