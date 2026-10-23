import FullHessianRank.ActualSaddle
import AmbientPairing.SelectedPairing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ComponentAmbientHessian
noncomputable section
open Matrix Equiv ComponentChartJacobian ComponentFullHessianRank AmbientPairing

theorem upper_cross_row (k : ℕ) (x : Remaining k → ℂ) (s : Fin 4) :
    (actualCross k).mulVec x (Sum.inl s) =
      ComponentUpperSeed.jac 3 s * x (Sum.inl ()) +
      ∑ c : Fin 3, ComponentUpperSeed.jac c.castSucc s *
        ∑ a : Fin (k+1), (finCofactorMatrix k).mulVec (seedLambda k) a * x (Sum.inr (a,c)) := by
  have hleft (a : Fin (k+1)) (c : Fin 3) : actualCross k (Sum.inl s) (Sum.inr (a,c)) =
      ComponentUpperSeed.jac c.castSucc s * (finCofactorMatrix k).mulVec (seedLambda k) a := by
    change hessian k (bVar (ComponentUpperSeed.selected s)) (lVar (a,c)) = _
    rw [hessian_symmetric]
    exact hessian_left_selected_upper k a c s
  have hW : actualCross k (Sum.inl s) (Sum.inl ()) = ComponentUpperSeed.jac 3 s :=
    hessian_selected_b_w00 k s
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_unique, hleft, hW]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The four selected upper rows force the W00 component and all three
weighted lower-left column sums to vanish. -/
theorem actualCross_kernel_upper_constraints (k : ℕ) (x : Remaining k → ℂ)
    (hx : (actualCross k).mulVec x = 0) :
    x (Sum.inl ()) = 0 ∧ ∀ c : Fin 3,
      (∑ a : Fin (k+1), (finCofactorMatrix k).mulVec (seedLambda k) a * x (Sum.inr (a,c))) = 0 := by
  let v : Fin 4 → ℂ := Fin.lastCases (x (Sum.inl ()))
    (fun c => ∑ a, (finCofactorMatrix k).mulVec (seedLambda k) a * x (Sum.inr (a,c)))
  have hv : ComponentUpperSeed.jac.transpose.mulVec v = 0 := by
    ext s
    have hs := congrFun hx (Sum.inl s)
    rw [upper_cross_row] at hs
    change (∑ c, ComponentUpperSeed.jac c s * v c) = 0
    rw [Fin.sum_univ_castSucc]
    simp only [v, Fin.lastCases_castSucc, Fin.lastCases_last]
    rw [show Fin.last 3 = (3 : Fin 4) from by decide]
    simpa only [add_comm, Pi.zero_apply] using hs
  have hdet : ComponentUpperSeed.jac.transpose.det ≠ 0 := by
    rw [Matrix.det_transpose, ComponentUpperSeed.jac_det]
    norm_num
  have hv0 : v = 0 := Matrix.mulVec_injective_of_det_ne_zero hdet (hv.trans (Matrix.mulVec_zero _).symm)
  constructor
  · have hh := congrFun hv0 (Fin.last 3)
    simpa only [v, Fin.lastCases_last, Pi.zero_apply] using hh
  · intro c
    have hh := congrFun hv0 c.castSucc
    simpa only [v, Fin.lastCases_castSucc, Pi.zero_apply] using hh

#print axioms actualCross_kernel_upper_constraints
end
end ComponentAmbientHessian
