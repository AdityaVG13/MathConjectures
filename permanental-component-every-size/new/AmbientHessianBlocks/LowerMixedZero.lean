import AmbientHessianBlocks.SameRow
import AmbientPairing.ActualPairing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ComponentAmbientHessian
noncomputable section
open MvPolynomial Matrix Equiv ComponentChartJacobian AmbientPairing

theorem upper_replaced_column_zero (c : Fin 3) :
    (ComponentUpperSeed.U.updateCol c ComponentUpperSeed.v).permanent = 0 := by
  fin_cases c <;> rw [PrimitiveFamily.expand3]
  all_goals norm_num [Fin.sum_univ_succ, Fin.prod_univ_succ, PrimitiveFamily.enumerate3,
    PrimitiveFamily.q0, PrimitiveFamily.q1, PrimitiveFamily.q2, PrimitiveFamily.q3,
    PrimitiveFamily.q4, PrimitiveFamily.q5, Matrix.submatrix, Matrix.updateCol_apply,
    ComponentUpperSeed.U, ComponentUpperSeed.v, ComponentUpperSeed.B]

theorem upper_linear_coefficient_zero (c : Fin 3) :
    linearCoefficient ComponentUpperSeed.U ComponentUpperSeed.v
      (fun j => if j = c then 1 else 0) = 0 := by
  unfold linearCoefficient
  simp [upper_replaced_column_zero]

/-- Every L-W block entry of the actual ambient Hessian vanishes at the seed,
including the same-row cases. No lower permanent vanishing is used here. -/
theorem hessian_l_w (k : ℕ) (a b : Fin (k+1)) (c : Fin 3) (j : Fin (k+1)) :
    hessian k (lVar (a,c)) (wVar (b,j)) = 0 := by
  by_cases hab : a = b
  · apply hessian_same_row
    simp [entryEquiv, lVar, wVar, hab]
  · rw [hessian_rows k _ _ (by simpa [entryEquiv, lVar, wVar] using hab)]
    have he : ((Matrix.fromBlocks ComponentUpperSeed.U (seedRight k) 0
        (SparseSeed.finArrowhead k)).updateRow (entryEquiv k (lVar (a,c))).1
        (fun d => if d = (entryEquiv k (lVar (a,c))).2 then 1 else 0) |>.updateRow
        (entryEquiv k (wVar (b,j))).1
        (fun d => if d = (entryEquiv k (wVar (b,j))).2 then 1 else 0)) =
      AmbientRestriction.addTop (AmbientRestriction.leftTop ComponentUpperSeed.U)
        (AmbientRestriction.rightTop ComponentUpperSeed.v (seedLambda k))
        (bottomOne ((SparseSeed.finArrowhead k).updateRow b (fun d => if d = j then 1 else 0))
          (fun d => if d = c then 1 else 0) a) := by
      apply Matrix.ext
      intro i d
      cases i with
      | inl i => cases d <;>
          simp [Matrix.updateRow_apply, Matrix.fromBlocks, AmbientRestriction.addTop,
            AmbientRestriction.leftTop, AmbientRestriction.rightTop, seedRight_factor,
            entry_lVar, entryEquiv, lVar, wVar]
      | inr i => cases d <;> by_cases hia : i = a <;> by_cases hib : i = b <;>
          simp_all [Matrix.updateRow_apply, Matrix.fromBlocks, AmbientRestriction.addTop,
            bottomOne, entry_lVar, entryEquiv, lVar, wVar]
    rw [he, permanent_one_lower_row, upper_linear_coefficient_zero, zero_mul]

#print axioms upper_replaced_column_zero
#print axioms hessian_l_w
end
end ComponentAmbientHessian
