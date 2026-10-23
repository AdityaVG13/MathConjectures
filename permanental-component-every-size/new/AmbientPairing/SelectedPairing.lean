import AmbientPairing.ActualPairing

namespace AmbientPairing
open Matrix Finset MvPolynomial ComponentChartJacobian ComponentAmbientHessian
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
noncomputable section

/-- Actual finite-index cofactor matrix of the lower seed. -/
def finCofactorMatrix (k : ℕ) : Matrix (Fin (k+1)) (Fin (k+1)) ℂ :=
  fun a j => ((SparseSeed.finArrowhead k).submatrix a.succAbove j.succAbove).permanent

theorem permanent_updateRow_expansion {m : ℕ}
    (A : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) (a : Fin (m+1)) (v : Fin (m+1) → ℂ) :
    (A.updateRow a v).permanent =
      ∑ j, v j * (A.submatrix a.succAbove j.succAbove).permanent := by
  rw [← Matrix.permanent_transpose, ExceptionalExpansion.permanent_expand_column _ a]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.transpose_apply, Matrix.updateRow_self]
  congr 1
  rw [← Matrix.permanent_transpose]
  congr 1
  ext i d
  simp [Matrix.submatrix, Matrix.updateRow_apply, Fin.succAbove_ne]

theorem lower_row_permanent (k : ℕ) (a : Fin (k+1)) :
    ((SparseSeed.finArrowhead k).updateRow a (seedLambda k)).permanent =
      (finCofactorMatrix k).mulVec (seedLambda k) a := by
  rw [permanent_updateRow_expansion]
  simp [Matrix.mulVec, dotProduct, finCofactorMatrix, mul_comm]

def selectedUpperRow : Fin 4 → Fin 3 := ![0,0,0,1]
def selectedUpperCol : Fin 4 → Fin 3 := ![0,1,2,0]

theorem selected_upper (k : ℕ) (s : Fin 4) :
    selected k (Sum.inl s) = bVar (selectedUpperRow s, (selectedUpperCol s).castSucc) := by
  fin_cases s <;> rfl

/-- Finite symbolic coefficient identity at the explicitly certified upper seed. -/
theorem selected_coefficient (c : Fin 3) (s : Fin 4) :
    linearCoefficient
      (ComponentUpperSeed.U.updateRow (selectedUpperRow s)
        (fun j => if j = selectedUpperCol s then 1 else 0))
      (Function.update ComponentUpperSeed.v (selectedUpperRow s) 0)
      (fun j => if j = c then 1 else 0) = ComponentUpperSeed.jac c.castSucc s := by
  fin_cases c <;> fin_cases s <;>
    norm_num [linearCoefficient, ComponentUpperSeed.jac, PrimitiveFamily.expand3,
      Fin.sum_univ_succ, Fin.prod_univ_succ, PrimitiveFamily.enumerate3,
      PrimitiveFamily.q0, PrimitiveFamily.q1, PrimitiveFamily.q2, PrimitiveFamily.q3,
      PrimitiveFamily.q4, PrimitiveFamily.q5, Matrix.submatrix, Fin.succAbove,
      ComponentUpperSeed.genericB, ComponentUpperSeed.selected,
      ComponentUpperSeed.U, ComponentUpperSeed.v, ComponentUpperSeed.B,
      selectedUpperRow, selectedUpperCol, Matrix.updateRow, Matrix.updateCol, Function.update]

/-- The four selected upper normal columns have exactly the claimed L-U pairing. -/
theorem hessian_left_selected_upper (k : ℕ) (a : Fin (k+1)) (c : Fin 3) (s : Fin 4) :
    hessian k (lVar (a,c)) (selected k (Sum.inl s)) =
      ComponentUpperSeed.jac c.castSucc s * (finCofactorMatrix k).mulVec (seedLambda k) a := by
  rw [selected_upper, hessian_left_upper, selected_coefficient, lower_row_permanent]

/-- The selected proportionality normal columns have exactly the claimed T-P pairing. -/
theorem hessian_left_selected_right (k : ℕ) (a : Fin (k+1)) (c : Fin 3)
    (i : Fin 2) (j : Fin k) :
    hessian k (lVar (a,c)) (selected k (Sum.inr (Sum.inr (Sum.inr (i,j))))) =
      ComponentUpperSeed.T c i.succ * finCofactorMatrix k a j.succ := by
  have hv : selected k (Sum.inr (Sum.inr (Sum.inr (i,j)))) =
      rightVariable k i.succ j.succ := rfl
  rw [hv, hessian_left_right]
  rfl

end
end AmbientPairing
#print axioms AmbientPairing.hessian_left_selected_upper
#print axioms AmbientPairing.hessian_left_selected_right
