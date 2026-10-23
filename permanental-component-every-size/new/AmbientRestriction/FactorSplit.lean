import AmbientRestriction.SupportedSplits
import BlockPermanent.BlockPermanent

namespace AmbientRestriction
open Finset Equiv
set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

def survivingUpper (U : Matrix (Fin 3) (Fin 3) ℂ) (k : Fin 3 → ℂ) (r : Fin 3) :
    Matrix (Fin 3) (Fin 3) ℂ := fun i j => if i = r then U i j else k j

private def exchangeRows (r : Fin 3) (a b : n) : Equiv.Perm (Fin 3 ⊕ n) :=
  Equiv.swap (Sum.inl (r.succAbove 0)) (Sum.inr a) *
    Equiv.swap (Sum.inl (r.succAbove 1)) (Sum.inr b)

omit [Fintype n] in
private theorem factor_split_matrix (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ)
    (lam : n → ℂ) (W : Matrix n n ℂ) (a b : n) (hab : a ≠ b) (r : Fin 3) :
    (splitTop {r} (leftTop U) (rightTop v lam) (bottomTwo W k a b)).submatrix (exchangeRows r a b) id =
      Matrix.fromBlocks (survivingUpper U k r) 0 0
        ((W.updateRow a (v (r.succAbove 0) • lam)).updateRow b (v (r.succAbove 1) • lam)) := by
  have hsucc : (2 : Fin 3).succAbove (1 : Fin 2) = 1 := by decide
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      fin_cases r <;> fin_cases i <;>
        simp [hsucc, Matrix.submatrix, Matrix.fromBlocks, exchangeRows, Equiv.Perm.mul_apply,
          Equiv.swap_apply_def, splitTop, leftTop, rightTop, bottomTwo, survivingUpper, hab, Ne.symm hab]
    | inr j =>
      fin_cases r <;> fin_cases i <;>
        simp [hsucc, Matrix.submatrix, Matrix.fromBlocks, exchangeRows, Equiv.Perm.mul_apply,
          Equiv.swap_apply_def, splitTop, leftTop, rightTop, bottomTwo, hab, Ne.symm hab]
  | inr i =>
    cases j with
    | inl j =>
      by_cases hia : i = a <;> by_cases hib : i = b <;>
        fin_cases r <;>
        simp_all [Matrix.submatrix, Matrix.fromBlocks, exchangeRows, Equiv.Perm.mul_apply,
          Equiv.swap_apply_def, splitTop, leftTop, rightTop, bottomTwo]
    | inr j =>
      by_cases hia : i = a <;> by_cases hib : i = b <;>
        fin_cases r <;>
        simp_all [Matrix.submatrix, Matrix.fromBlocks, exchangeRows, Equiv.Perm.mul_apply,
          Equiv.swap_apply_def, splitTop, leftTop, rightTop, bottomTwo]

/-- Row permutation exhibits each surviving term as a genuine block diagonal permanent. -/
theorem permanent_split_factor (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ)
    (lam : n → ℂ) (W : Matrix n n ℂ) (a b : n) (hab : a ≠ b) (r : Fin 3) :
    (splitTop {r} (leftTop U) (rightTop v lam) (bottomTwo W k a b)).permanent =
      (survivingUpper U k r).permanent *
        ((W.updateRow a (v (r.succAbove 0) • lam)).updateRow b (v (r.succAbove 1) • lam)).permanent := by
  rw [← Matrix.permanent_permute_cols (exchangeRows r a b),
    factor_split_matrix U v k lam W a b hab r,
    ComponentBlockPermanent.permanent_fromBlocks_zero_lower]

end AmbientRestriction

#print axioms AmbientRestriction.permanent_split_factor
