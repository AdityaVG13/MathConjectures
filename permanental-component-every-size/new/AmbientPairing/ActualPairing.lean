import AmbientPairing.Crossing
import AmbientPairing.DerivativeRows
import AmbientHessianBlocks.Definitions

namespace AmbientPairing
open MvPolynomial ComponentChartJacobian ComponentAmbientHessian
set_option backward.isDefEq.respectTransparency false
noncomputable section

def seedRight (k : ℕ) : Matrix (Fin 3) (Fin (k+1)) ℂ :=
  fun i j => Fin.cases (ComponentUpperSeed.v i) (fun _ => 2 * ComponentUpperSeed.v i) j

theorem seed_matrix (k : ℕ) :
    (fun i j => seed k ((entryEquiv k).symm (i,j))) =
      Matrix.fromBlocks ComponentUpperSeed.U (seedRight k) 0 (SparseSeed.finArrowhead k) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => rfl
    | inr j => refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  | inr i => cases j <;> rfl

/-- Genuine ambient Hessian entries expressed as coordinate row replacements. -/
theorem hessian_rows (k : ℕ) (x y : Variables k)
    (hxy : (entryEquiv k x).1 ≠ (entryEquiv k y).1) :
    hessian k x y =
      ((Matrix.fromBlocks ComponentUpperSeed.U (seedRight k) 0 (SparseSeed.finArrowhead k)).updateRow
        (entryEquiv k x).1 (fun j => if j = (entryEquiv k x).2 then 1 else 0) |>.updateRow
        (entryEquiv k y).1 (fun j => if j = (entryEquiv k y).2 then 1 else 0)).permanent := by
  unfold hessian actualPolynomial actualAmbient
  rw [eval_generic_mixed_rows _ _ _ _ hxy, seed_matrix]

/-- Index of an arbitrary top-right entry, including the distinguished v column. -/
def rightVariable (k : ℕ) (r : Fin 3) (j : Fin (k+1)) : Variables k :=
  (entryEquiv k).symm (Sum.inl r, Sum.inr j)

@[simp] theorem entry_rightVariable (k : ℕ) (r : Fin 3) (j : Fin (k+1)) :
    entryEquiv k (rightVariable k r j) = (Sum.inl r, Sum.inr j) :=
  (entryEquiv k).apply_symm_apply _

@[simp] theorem entry_lVar (k : ℕ) (a : Fin (k+1)) (c : Fin 3) :
    entryEquiv k (lVar (a,c)) = (Sum.inr a, Sum.inl c) := rfl

/-- Exact L-R block of the actual ambient Hessian. -/
theorem hessian_left_right (k : ℕ) (a j : Fin (k+1)) (c r : Fin 3) :
    hessian k (lVar (a,c)) (rightVariable k r j) =
      (ComponentUpperSeed.U.submatrix r.succAbove c.succAbove).permanent *
        ((SparseSeed.finArrowhead k).submatrix a.succAbove j.succAbove).permanent := by
  rw [hessian_rows k _ _ (by simp)]
  have he : ((Matrix.fromBlocks ComponentUpperSeed.U (seedRight k) 0
        (SparseSeed.finArrowhead k)).updateRow (entryEquiv k (lVar (a,c))).1
        (fun d => if d = (entryEquiv k (lVar (a,c))).2 then 1 else 0) |>.updateRow
        (entryEquiv k (rightVariable k r j)).1
        (fun d => if d = (entryEquiv k (rightVariable k r j)).2 then 1 else 0)) =
      crossingMatrix ComponentUpperSeed.U (seedRight k) (SparseSeed.finArrowhead k) r c a j := by
    ext i d
    cases i with
    | inl i => cases d <;> by_cases hi : i = r <;>
        simp_all [Matrix.updateRow_apply, Matrix.fromBlocks, crossingMatrix,
          entry_lVar, entry_rightVariable]
    | inr i => cases d <;> by_cases hi : i = a <;>
        simp_all [Matrix.updateRow_apply, Matrix.fromBlocks, crossingMatrix,
          entry_lVar, entry_rightVariable]
  rw [he, permanent_crossing_minors]

/-- The lower seed row used by the rank-one upper-right block. -/
def seedLambda (k : ℕ) : Fin (k+1) → ℂ := Fin.cases 1 (fun _ => 2)

theorem seedRight_factor (k : ℕ) (i : Fin 3) (j : Fin (k+1)) :
    seedRight k i j = ComponentUpperSeed.v i * seedLambda k j := by
  refine Fin.cases ?_ (fun j => ?_) j <;> simp [seedRight, seedLambda, mul_comm]

@[simp] theorem entry_upperVariable (k : ℕ) (r d : Fin 3) :
    entryEquiv k (bVar (r,d.castSucc)) = (Sum.inl r, Sum.inl d) := by
  simp [entryEquiv, bVar]

/-- Exact L-U block, with the coefficient expressed in column-replacement permanents. -/
theorem hessian_left_upper (k : ℕ) (a : Fin (k+1)) (c r d : Fin 3) :
    hessian k (lVar (a,c)) (bVar (r,d.castSucc)) =
      linearCoefficient (ComponentUpperSeed.U.updateRow r (fun j => if j = d then 1 else 0))
        (Function.update ComponentUpperSeed.v r 0) (fun j => if j = c then 1 else 0) *
        ((SparseSeed.finArrowhead k).updateRow a (seedLambda k)).permanent := by
  rw [hessian_rows k _ _ (by simp)]
  have he : ((Matrix.fromBlocks ComponentUpperSeed.U (seedRight k) 0
        (SparseSeed.finArrowhead k)).updateRow (entryEquiv k (lVar (a,c))).1
        (fun j => if j = (entryEquiv k (lVar (a,c))).2 then 1 else 0) |>.updateRow
        (entryEquiv k (bVar (r,d.castSucc))).1
        (fun j => if j = (entryEquiv k (bVar (r,d.castSucc))).2 then 1 else 0)) =
      AmbientRestriction.addTop
        (AmbientRestriction.leftTop (ComponentUpperSeed.U.updateRow r (fun j => if j = d then 1 else 0)))
        (AmbientRestriction.rightTop (Function.update ComponentUpperSeed.v r 0) (seedLambda k))
        (bottomOne (SparseSeed.finArrowhead k) (fun j => if j = c then 1 else 0) a) := by
    ext i j
    cases i with
    | inl i => cases j <;> by_cases hi : i = r <;>
        simp_all [Matrix.updateRow_apply, Matrix.fromBlocks, AmbientRestriction.addTop,
          AmbientRestriction.leftTop, AmbientRestriction.rightTop, seedRight_factor,
          Function.update]
    | inr i => cases j <;> by_cases hi : i = a <;>
        simp_all [Matrix.updateRow_apply, Matrix.fromBlocks, AmbientRestriction.addTop, bottomOne]
  rw [he, permanent_one_lower_row]

end
end AmbientPairing
#print axioms AmbientPairing.hessian_left_right

#print axioms AmbientPairing.hessian_left_upper
