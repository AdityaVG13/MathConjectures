import SparseSeed.ConstantRows

namespace SparseSeed
open Finset Equiv

/-- The fixed vector used in the lower-seed rank-one perturbation. -/
def lambda (l : ℕ) : Option (Fin l) → ℂ
  | none => 1
  | some _ => 2

/-- Replace the two named rows by the vector `lambda`. -/
def twoRows (l : ℕ) (a b : Option (Fin l)) : Matrix (Option (Fin l)) (Option (Fin l)) ℂ :=
  fun i j => if i = a ∨ i = b then lambda l j else arrowhead l i j

private theorem hub_leaf_minor_hub (l : ℕ) (a : Fin l) :
    (twoRows l none (some a)).submatrix some some = constantRows {a} (fun _ => 2) := by
  ext i j
  by_cases hi : i = a <;> simp [Matrix.submatrix, twoRows, lambda, arrowhead, constantRows, hi]

private theorem hub_leaf_minor_leaf (l : ℕ) (a t : Fin l) :
    (twoRows l none (some a)).submatrix (fun i => swap none (some t) (some i)) some =
      constantRows {a, t} (fun _ => 2) := by
  ext i j
  by_cases hia : i = a <;> by_cases hit : i = t <;>
    simp_all [Matrix.submatrix, twoRows, lambda, arrowhead, constantRows,
      Equiv.swap_apply_of_ne_of_ne]

/-- The actual two-row replacement permanent for a hub and leaf, uniformly in size. -/
theorem permanent_twoRows_hub_leaf (l : ℕ) (a : Fin l) :
    (twoRows l none (some a)).permanent = 8 * (l : ℂ) - 4 := by
  rw [permanent_option_hub_column, Fintype.sum_option]
  have hhub : (twoRows l none (some a)).submatrix (fun i => swap none none (some i)) some =
      constantRows {a} (fun _ => 2) := by simpa using hub_leaf_minor_hub l a
  rw [hhub, permanent_constantRows]
  have hleaf (t : Fin l) :
      ((twoRows l none (some a)).submatrix (fun i => swap none (some t) (some i)) some).permanent =
        8 + if t = a then (-6 : ℂ) else 0 := by
    rw [hub_leaf_minor_leaf, permanent_constantRows]
    by_cases ht : t = a
    · subst t; norm_num
    · simp [ht, Ne.symm ht]
      norm_num
  simp_rw [hleaf]
  have hcol (t : Fin l) : twoRows l none (some a) (some t) none = 1 := by
    by_cases ht : t = a <;> simp [twoRows, lambda, arrowhead, ht]
  simp only [hcol, one_mul]
  simp [twoRows, lambda, Finset.sum_add_distrib]
  ring

private theorem leaves_minor_hub (l : ℕ) (a b : Fin l) :
    (twoRows l (some a) (some b)).submatrix some some = constantRows {a, b} (fun _ => 2) := by
  ext i j
  by_cases hia : i = a <;> by_cases hib : i = b <;>
    simp [Matrix.submatrix, twoRows, lambda, arrowhead, constantRows, hia, hib]

private theorem leaves_minor_leaf (l : ℕ) (a b t : Fin l) :
    (twoRows l (some a) (some b)).submatrix (fun i => swap none (some t) (some i)) some =
      constantRows {a, b, t} (fun i => if i = t then 1 else 2) := by
  ext i j
  by_cases hia : i = a <;> by_cases hib : i = b <;> by_cases hit : i = t <;>
    simp_all [Matrix.submatrix, twoRows, lambda, arrowhead, constantRows,
      Equiv.swap_apply_of_ne_of_ne]

/-- The actual two-row replacement permanent for distinct leaves, uniformly in size. -/
theorem permanent_twoRows_distinct_leaves (l : ℕ) (a b : Fin l) (hab : a ≠ b) :
    (twoRows l (some a) (some b)).permanent = 16 * (l : ℂ) - 40 := by
  rw [permanent_option_hub_column, Fintype.sum_option]
  have hhub : (twoRows l (some a) (some b)).submatrix (fun i => swap none none (some i)) some =
      constantRows {a, b} (fun _ => 2) := by simpa using leaves_minor_hub l a b
  rw [hhub, permanent_constantRows]
  have hleaf (t : Fin l) :
      ((twoRows l (some a) (some b)).submatrix (fun i => swap none (some t) (some i)) some).permanent =
        24 + (if t = a then (-20 : ℂ) else 0) + (if t = b then (-20 : ℂ) else 0) := by
    rw [leaves_minor_leaf, permanent_constantRows]
    by_cases hta : t = a
    · subst t; simp [hab, Ne.symm hab]; norm_num
    by_cases htb : t = b
    · subst t; simp [hab, Ne.symm hab]; norm_num
    · simp [hta, htb, Ne.symm hta, Ne.symm htb, hab, Nat.factorial]
      norm_num
  simp_rw [hleaf]
  have hcol (t : Fin l) : twoRows l (some a) (some b) (some t) none = 1 := by
    by_cases hta : t = a <;> by_cases htb : t = b <;>
      simp [twoRows, lambda, arrowhead, hta, htb]
  simp only [hcol, one_mul]
  simp [twoRows, arrowhead, hab, Finset.sum_add_distrib]
  ring

end SparseSeed

#print axioms SparseSeed.permanent_twoRows_hub_leaf
#print axioms SparseSeed.permanent_twoRows_distinct_leaves
