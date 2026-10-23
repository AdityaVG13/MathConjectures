import AmbientRestriction.Splitting

namespace AmbientRestriction
open Finset Equiv
set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

def leftTop (U : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3 ⊕ n) ℂ
  | i, Sum.inl j => U i j
  | _, Sum.inr _ => 0

def rightTop (v : Fin 3 → ℂ) (lam : n → ℂ) : Matrix (Fin 3) (Fin 3 ⊕ n) ℂ
  | _, Sum.inl _ => 0
  | i, Sum.inr j => v i * lam j

/-- The two differentiated lower rows are supported only in the three left columns. -/
def bottomTwo (W : Matrix n n ℂ) (k : Fin 3 → ℂ) (a b : n) : Matrix n (Fin 3 ⊕ n) ℂ
  | i, Sum.inl j => if i = a ∨ i = b then k j else 0
  | i, Sum.inr j => if i = a ∨ i = b then 0 else W i j

/-- Only terms with one left-supported top row survive after differentiating two lower rows. -/
theorem permanent_split_zero (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ)
    (lam : n → ℂ) (W : Matrix n n ℂ) (a b : n) (hab : a ≠ b)
    (s : Finset (Fin 3)) (hs : s.card ≠ 1) :
    (splitTop s (leftTop U) (rightTop v lam) (bottomTwo W k a b)).permanent = 0 := by
  let f : Fin 3 ⊕ n → ℕ
    | Sum.inl i => if i ∈ s then 1 else 0
    | Sum.inr i => if i = a ∨ i = b then 1 else 0
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
        by_cases hi : i = a ∨ i = b <;> simp_all [f, g, splitTop, bottomTwo]
      | inr j =>
        by_cases hi : i = a ∨ i = b <;> simp_all [f, g, splitTop, bottomTwo]
  · have he (i : n) : (if i = a ∨ i = b then (1 : ℕ) else 0) =
        (if i = a then 1 else 0) + (if i = b then 1 else 0) := by
      by_cases hia : i = a <;> by_cases hib : i = b <;> simp_all
    have hf : (∑ i, f i) = s.card + 2 := by
      rw [Fintype.sum_sum_type]
      simp only [f, he, Finset.sum_add_distrib]
      simp
    have hg : (∑ i, g i) = 3 := by simp [g, Fintype.sum_sum_type]
    rw [hf, hg]
    omega

/-- The actual two-lower-row replacement permanent is a sum of exactly three surviving terms. -/
theorem permanent_addTop_three (U : Matrix (Fin 3) (Fin 3) ℂ) (v k : Fin 3 → ℂ)
    (lam : n → ℂ) (W : Matrix n n ℂ) (a b : n) (hab : a ≠ b) :
    (addTop (leftTop U) (rightTop v lam) (bottomTwo W k a b)).permanent =
      ∑ r : Fin 3, (splitTop {r} (leftTop U) (rightTop v lam) (bottomTwo W k a b)).permanent := by
  rw [permanent_addTop]
  rw [permanent_split_zero U v k lam W a b hab ∅ (by simp),
    permanent_split_zero U v k lam W a b hab {0, 1} (by decide),
    permanent_split_zero U v k lam W a b hab {0, 2} (by decide),
    permanent_split_zero U v k lam W a b hab {1, 2} (by decide),
    permanent_split_zero U v k lam W a b hab {0, 1, 2} (by decide)]
  simp [Fin.sum_univ_succ]
  ring

end AmbientRestriction

#print axioms AmbientRestriction.permanent_split_zero
#print axioms AmbientRestriction.permanent_addTop_three
