import AmbientRestriction.QuadraticFactor

namespace AmbientPairing
open AmbientRestriction
open Finset Equiv
set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The differentiated lower row is supported only in the three left columns. -/
def bottomOne (W : Matrix n n ℂ) (k : Fin 3 → ℂ) (a : n) : Matrix n (Fin 3 ⊕ n) ℂ
  | i, Sum.inl j => if i = a then k j else 0
  | i, Sum.inr j => if i = a then 0 else W i j

/-- Only terms with two left-supported top rows survive after differentiating one lower row. -/
theorem permanent_split_zero (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ)
    (lam : n → ℂ) (W : Matrix n n ℂ) (a : n) 
    (s : Finset (Fin 3)) (hs : s.card ≠ 2) :
    (splitTop s (leftTop U) (rightTop v lam) (bottomOne W k a)).permanent = 0 := by
  let f : Fin 3 ⊕ n → ℕ
    | Sum.inl i => if i ∈ s then 1 else 0
    | Sum.inr i => if i = a then 1 else 0
  let g : Fin 3 ⊕ n → ℕ
    | Sum.inl _ => 1
    | Sum.inr _ => 0
  apply permanent_zero_of_partition _ f g
  · intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        by_cases hi : i ∈ s <;> simp_all [f, g, splitTop, rightTop]
      | inr j =>
        by_cases hi : i ∈ s <;> simp_all [f, g, splitTop, leftTop]
    | inr i =>
      cases j with
      | inl j =>
        by_cases hi : i = a <;> simp_all [f, g, splitTop, bottomOne]
      | inr j =>
        by_cases hi : i = a <;> simp_all [f, g, splitTop, bottomOne]
  · have hf : (∑ i, f i) = s.card + 1 := by
      rw [Fintype.sum_sum_type]
      simp [f]
    have hg : (∑ i, g i) = 3 := by simp [g, Fintype.sum_sum_type]
    rw [hf, hg]
    omega

/-- Exactly two top rows must remain in the left block. -/
theorem permanent_addTop_three (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ)
    (lam : n → ℂ) (W : Matrix n n ℂ) (a : n) :
    (addTop (leftTop U) (rightTop v lam) (bottomOne W k a)).permanent =
      ∑ r : Fin 3, (splitTop (Finset.univ.erase r) (leftTop U) (rightTop v lam)
        (bottomOne W k a)).permanent := by
  rw [AmbientRestriction.permanent_addTop]
  rw [permanent_split_zero U v k lam W a ∅ (by simp),
    permanent_split_zero U v k lam W a {0} (by decide),
    permanent_split_zero U v k lam W a {1} (by decide),
    permanent_split_zero U v k lam W a {2} (by decide),
    permanent_split_zero U v k lam W a {0, 1, 2} (by decide)]
  have h0 : Finset.univ.erase (0 : Fin 3) = {1, 2} := by decide
  have h1 : Finset.univ.erase (1 : Fin 3) = {0, 2} := by decide
  have h2 : Finset.univ.erase (2 : Fin 3) = {0, 1} := by decide
  simp [Fin.sum_univ_succ, h0, h1, h2]
  ring


omit [Fintype n] in
private theorem factor_split_matrix (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ)
    (lam : n → ℂ) (W : Matrix n n ℂ) (a : n) (r : Fin 3) :
    (splitTop (Finset.univ.erase r) (leftTop U) (rightTop v lam) (bottomOne W k a)).submatrix
      (Equiv.swap (Sum.inl r) (Sum.inr a)) id =
      Matrix.fromBlocks (U.updateRow r k) 0 0 (W.updateRow a (v r • lam)) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      by_cases hi : i = r <;>
        simp_all [Matrix.submatrix, Matrix.fromBlocks, Equiv.swap_apply_def,
          splitTop, leftTop, rightTop, bottomOne]
    | inr j =>
      by_cases hi : i = r <;>
        simp_all [Matrix.submatrix, Matrix.fromBlocks, Equiv.swap_apply_def,
          splitTop, leftTop, rightTop, bottomOne]
  | inr i =>
    cases j with
    | inl j =>
      by_cases hi : i = a <;>
        simp_all [Matrix.submatrix, Matrix.fromBlocks, Equiv.swap_apply_def,
          splitTop, leftTop, rightTop, bottomOne]
    | inr j =>
      by_cases hi : i = a <;>
        simp_all [Matrix.submatrix, Matrix.fromBlocks, Equiv.swap_apply_def,
          splitTop, leftTop, rightTop, bottomOne]

theorem permanent_split_factor (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ)
    (lam : n → ℂ) (W : Matrix n n ℂ) (a : n) (r : Fin 3) :
    (splitTop (Finset.univ.erase r) (leftTop U) (rightTop v lam) (bottomOne W k a)).permanent =
      (U.updateRow r k).permanent * (v r * (W.updateRow a lam).permanent) := by
  rw [← Matrix.permanent_permute_cols (Equiv.swap (Sum.inl r) (Sum.inr a)),
    factor_split_matrix U v k lam W a r,
    ComponentBlockPermanent.permanent_fromBlocks_zero_lower,
    Matrix.permanent_updateRow_smul]

/-- The upper linear coefficient, expressed using column-replacement permanents. -/
def linearCoefficient (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ) : ℂ :=
  ∑ c, k c * (U.updateCol c v).permanent

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

theorem linearCoefficient_eq (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ) :
    (∑ r, (U.updateRow r k).permanent * v r) = linearCoefficient U v k := by
  norm_num [linearCoefficient, Fin.sum_univ_succ, permanent_three, Matrix.updateRow, Matrix.updateCol, Function.update]
  ring

/-- Exact one-crossing factorization for arbitrary data and every finite lower size. -/
theorem permanent_one_lower_row (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ)
    (lam : n → ℂ) (W : Matrix n n ℂ) (a : n) :
    (addTop (leftTop U) (rightTop v lam) (bottomOne W k a)).permanent =
      linearCoefficient U v k * (W.updateRow a lam).permanent := by
  rw [permanent_addTop_three]
  simp_rw [permanent_split_factor]
  rw [← linearCoefficient_eq U v k, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  ring

end AmbientPairing
#print axioms AmbientPairing.permanent_one_lower_row
