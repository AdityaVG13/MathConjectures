import AmbientPairing.OneRow

namespace AmbientPairing
open Finset Equiv
set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Top row r is a right-coordinate row, and bottom row a is a left-coordinate row. -/
def crossingMatrix (U : Matrix (Fin 3) (Fin 3) ℂ) (R : Matrix (Fin 3) n ℂ)
    (W : Matrix n n ℂ) (r c : Fin 3) (a j : n) : Matrix (Fin 3 ⊕ n) (Fin 3 ⊕ n) ℂ
  | Sum.inl i, Sum.inl d => if i = r then 0 else U i d
  | Sum.inl i, Sum.inr b => if i = r then (if b = j then 1 else 0) else R i b
  | Sum.inr i, Sum.inl d => if i = a then (if d = c then 1 else 0) else 0
  | Sum.inr i, Sum.inr b => if i = a then 0 else W i b

/-- Swapping the two differentiated rows restores block-upper-triangularity. -/
theorem permanent_crossing (U : Matrix (Fin 3) (Fin 3) ℂ) (R : Matrix (Fin 3) n ℂ)
    (W : Matrix n n ℂ) (r c : Fin 3) (a j : n) :
    (crossingMatrix U R W r c a j).permanent =
      (U.updateRow r (fun d => if d = c then 1 else 0)).permanent *
      (W.updateRow a (fun b => if b = j then 1 else 0)).permanent := by
  have he : (crossingMatrix U R W r c a j).submatrix
      (Equiv.swap (Sum.inl r) (Sum.inr a)) id =
      Matrix.fromBlocks (U.updateRow r (fun d => if d = c then 1 else 0))
        (R.updateRow r 0) 0 (W.updateRow a (fun b => if b = j then 1 else 0)) := by
    ext i d
    cases i with
    | inl i => cases d <;> by_cases hi : i = r <;>
        simp_all [Matrix.submatrix, Matrix.fromBlocks, Equiv.swap_apply_def, crossingMatrix]
    | inr i => cases d <;> by_cases hi : i = a <;>
        simp_all [Matrix.submatrix, Matrix.fromBlocks, Equiv.swap_apply_def, crossingMatrix]
  rw [← Matrix.permanent_permute_cols (Equiv.swap (Sum.inl r) (Sum.inr a)), he,
    ComponentBlockPermanent.permanent_fromBlocks_zero_lower]

theorem permanent_updateRow_coordinate {m : ℕ}
    (A : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) (r c : Fin (m+1)) :
    (A.updateRow r (fun d => if d = c then 1 else 0)).permanent =
      (A.submatrix r.succAbove c.succAbove).permanent := by
  rw [← Matrix.permanent_transpose, ExceptionalExpansion.permanent_expand_column _ r]
  simp only [Matrix.transpose_apply, Matrix.updateRow_self]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Matrix.permanent_transpose]
  congr 1
  ext i j
  simp [Matrix.submatrix, Matrix.updateRow_apply, Fin.succAbove_ne]

/-- The crossing is exactly the product of standard deletion minors. -/
theorem permanent_crossing_minors {m : ℕ} (U : Matrix (Fin 3) (Fin 3) ℂ)
    (R : Matrix (Fin 3) (Fin (m+1)) ℂ) (W : Matrix (Fin (m+1)) (Fin (m+1)) ℂ)
    (r c : Fin 3) (a j : Fin (m+1)) :
    (crossingMatrix U R W r c a j).permanent =
      (U.submatrix r.succAbove c.succAbove).permanent *
      (W.submatrix a.succAbove j.succAbove).permanent := by
  rw [permanent_crossing, permanent_updateRow_coordinate, permanent_updateRow_coordinate]

end AmbientPairing
#print axioms AmbientPairing.permanent_crossing_minors
