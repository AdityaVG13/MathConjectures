import AmbientRestriction.FactorSplit
import ExceptionalExpansion

namespace AmbientRestriction
open Finset Equiv
set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The coefficient from the single retained upper column. -/
def beta (U : Matrix (Fin 3) (Fin 3) ℂ) (v : Fin 3 → ℂ) (c : Fin 3) : ℂ :=
  ∑ r : Fin 3, U r c * ∏ s : Fin 2, v (r.succAbove s)

def eta (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ) : ℂ :=
  k 0 * k 1 * beta U v 2 + k 0 * k 2 * beta U v 1 + k 1 * k 2 * beta U v 0

private theorem permanent_two (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M.permanent = M 0 0 * M 1 1 + M 1 0 * M 0 1 := by
  rw [ExceptionalExpansion.permanent_succ_column_zero]
  norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove]

private theorem permanent_three (M : Matrix (Fin 3) (Fin 3) ℂ) :
    M.permanent =
      M 0 0 * M 1 1 * M 2 2 + M 0 0 * M 1 2 * M 2 1 +
      M 0 1 * M 1 0 * M 2 2 + M 0 1 * M 1 2 * M 2 0 +
      M 0 2 * M 1 0 * M 2 1 + M 0 2 * M 1 1 * M 2 0 := by
  rw [ExceptionalExpansion.permanent_succ_column_zero]
  norm_num [Fin.sum_univ_succ, permanent_two, Matrix.submatrix, Fin.succAbove]
  ring

/-- The two identical k rows contribute the crucial factor of two. -/
theorem surviving_upper_sum (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ) :
    (∑ r : Fin 3, (survivingUpper U k r).permanent * v (r.succAbove 0) * v (r.succAbove 1)) =
      2 * eta U v k := by
  norm_num [Fin.sum_univ_succ, permanent_three, survivingUpper, eta, beta,
    Fin.prod_univ_succ, Fin.succAbove]
  ring

private theorem permanent_two_scaled_rows (W : Matrix n n ℂ) (lam : n → ℂ)
    (a b : n) (hab : a ≠ b) (x y : ℂ) :
    ((W.updateRow a (x • lam)).updateRow b (y • lam)).permanent =
      x * y * ((W.updateRow a lam).updateRow b lam).permanent := by
  rw [Matrix.permanent_updateRow_smul,
    Matrix.updateRow_comm W hab, Matrix.permanent_updateRow_smul,
    Matrix.updateRow_comm W (Ne.symm hab)]
  ring

/-- Actual uniform permanent identity for two lower-left row replacements. No upper
cofactor vanishing, genericity, or lower-size hypothesis is needed. -/
theorem permanent_two_lower_rows (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ)
    (lam : n → ℂ) (W : Matrix n n ℂ) (a b : n) (hab : a ≠ b) :
    (addTop (leftTop U) (rightTop v lam) (bottomTwo W k a b)).permanent =
      (2 * eta U v k) * ((W.updateRow a lam).updateRow b lam).permanent := by
  rw [permanent_addTop_three U v k lam W a b hab]
  simp_rw [permanent_split_factor U v k lam W a b hab,
    permanent_two_scaled_rows W lam a b hab]
  rw [← surviving_upper_sum U v k, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  ring

end AmbientRestriction

#print axioms AmbientRestriction.surviving_upper_sum
#print axioms AmbientRestriction.permanent_two_lower_rows
