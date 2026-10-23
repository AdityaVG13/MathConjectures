import AmbientPairing.LowerCofactor
import FullHessianRank.ActualSaddle

namespace AmbientPairing
open Matrix Finset ComponentChartJacobian ComponentAmbientHessian ComponentFullHessianRank
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem actualCross_upper_zero (k : ℕ) (s : Fin 4) :
    actualCross k (Sum.inl s) (Sum.inl ()) = ComponentUpperSeed.jac 3 s := by
  exact hessian_selected_b_w00 k s

theorem actualCross_right_zero (k : ℕ) (i : Fin 2) (j : Fin k) :
    actualCross k (Sum.inr (i,j)) (Sum.inl ()) = 0 := by
  exact hessian_v_nonLower k _ _ (nonLower_w _)

theorem actualCross_upper_left (k : ℕ) (s : Fin 4) (a : Fin (k+1)) (c : Fin 3) :
    actualCross k (Sum.inl s) (Sum.inr (a,c)) =
      ComponentUpperSeed.jac c.castSucc s * (finCofactorMatrix k).mulVec (seedLambda k) a := by
  change hessian k _ _ = _
  rw [hessian_symmetric]
  exact hessian_left_selected_upper k a c s

theorem actualCross_right_left (k : ℕ) (i : Fin 2) (j : Fin k) (a : Fin (k+1)) (c : Fin 3) :
    actualCross k (Sum.inr (i,j)) (Sum.inr (a,c)) =
      ComponentUpperSeed.T c i.succ * finCofactorMatrix k a j.succ := by
  change hessian k _ _ = _
  rw [hessian_symmetric]
  exact hessian_left_selected_right k a c i j

/-- The coefficient vector before multiplication by the invertible lower cofactor matrix. -/
def crossCoefficient (k : ℕ) (x : Isotropic k → ℂ) (c : Fin 3) : Fin (k+1) → ℂ :=
  fun a => seedLambda k a * (∑ s, ComponentUpperSeed.jac c.castSucc s * x (Sum.inl s)) +
    Fin.cases 0 (fun j => ∑ i : Fin 2, ComponentUpperSeed.T c i.succ * x (Sum.inr (i,j))) a

theorem actualCross_mul_left (k : ℕ) (x : Isotropic k → ℂ) (a : Fin (k+1)) (c : Fin 3) :
    (actualCross k).transpose.mulVec x (Sum.inr (a,c)) =
      (finCofactorMatrix k).mulVec (crossCoefficient k x c) a := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fintype.sum_sum_type,
    Fintype.sum_prod_type, actualCross_upper_left, actualCross_right_left,
    crossCoefficient, mul_add, Finset.sum_add_distrib]
  congr 1
  · simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, mul_zero, Fin.cases_succ, zero_add, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The actual cross-pairing has trivial left kernel. -/
theorem actualCross_transpose_kernel_zero (k : ℕ) (x : Isotropic k → ℂ)
    (hx : (actualCross k).transpose.mulVec x = 0) : x = 0 := by
  have hp : Function.Injective (finCofactorMatrix k).mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (det_finCofactorMatrix_ne_zero k)))
  have hc (c : Fin 3) : crossCoefficient k x c = 0 := by
    apply hp
    rw [Matrix.mulVec_zero]
    funext a
    rw [← actualCross_mul_left]
    exact congrFun hx (Sum.inr (a,c))
  have hu : ComponentUpperSeed.jac.mulVec (fun s => x (Sum.inl s)) = 0 := by
    funext c
    refine Fin.lastCases ?_ (fun c => ?_) c
    · have hh := congrFun hx (Sum.inl ())
      simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fintype.sum_sum_type,
        Fintype.sum_prod_type, actualCross_upper_zero, actualCross_right_zero] using hh
    · have hh := congrFun (hc c) 0
      simpa [crossCoefficient, seedLambda, Matrix.mulVec, dotProduct] using hh
  have hu0 : (fun s => x (Sum.inl s)) = 0 := by
    have hj : Function.Injective ComponentUpperSeed.jac.mulVec :=
      Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr
        (isUnit_iff_ne_zero.mpr (by rw [ComponentUpperSeed.jac_det]; norm_num)))
    apply hj
    simpa using hu
  have hr (j : Fin k) : (fun i : Fin 2 => x (Sum.inr (i,j))) = 0 := by
    let w : Fin 3 → ℂ := Fin.cases 0 (fun i => x (Sum.inr (i,j)))
    have hw : ComponentUpperSeed.T.mulVec w = 0 := by
      funext c
      have hh := congrFun (hc c) j.succ
      have hz (s : Fin 4) : x (Sum.inl s) = 0 := congrFun hu0 s
      simpa [crossCoefficient, hz, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, w] using hh
    have hw0 := ComponentUpperSeed.injective_on_first_zero w rfl hw
    funext i
    exact congrFun hw0 i.succ
  funext i
  rcases i with s | ⟨i,j⟩
  · exact congrFun hu0 s
  · exact congrFun (hr j) i

/-- The genuine selected ambient cross-pairing is injective, with no rank hypothesis. -/
theorem actualCross_transpose_injective (k : ℕ) :
    Function.Injective (actualCross k).transpose.mulVec := by
  intro x y h
  have hz : (actualCross k).transpose.mulVec (x-y) = 0 := by
    rw [Matrix.mulVec_sub, h, sub_self]
  exact sub_eq_zero.mp (actualCross_transpose_kernel_zero k (x-y) hz)

end
end AmbientPairing
#print axioms AmbientPairing.actualCross_mul_left

#print axioms AmbientPairing.actualCross_transpose_injective
