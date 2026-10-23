import SparseSeed.Arrowhead

namespace SparseSeed
open Finset Equiv

/-- An arrowhead with an arbitrary named hub and arbitrary hub weight. -/
def hubMatrix {n : Type*} [DecidableEq n] (hub : n) (c : ℂ) : Matrix n n ℂ :=
  fun i j => if i = hub then (if j = hub then c else 1)
    else if j = hub then 1 else if i = j then 1 else 0

private theorem hub_supported {n : Type*} [DecidableEq n] [Fintype n]
    (hub : n) (c : ℂ) (σ : Equiv.Perm n)
    (h : (∏ i, hubMatrix hub c (σ i) i) ≠ 0) : σ = Equiv.swap hub (σ hub) := by
  have hs (i : n) (hi : i ≠ hub) : σ i = hub ∨ σ i = i := by
    have hn : hubMatrix hub c (σ i) i ≠ 0 := by
      intro hz
      exact h (Finset.prod_eq_zero (Finset.mem_univ _) hz)
    by_cases hσ : σ i = hub
    · exact Or.inl hσ
    · right
      by_contra hh
      simp [hubMatrix, hσ, hi, hh] at hn
  ext x
  by_cases hh : σ hub = hub
  · by_cases hx : x = hub
    · subst x; simp [hh]
    · rcases hs x hx with hxh | hxx
      · exact (hx (σ.injective (hxh.trans hh.symm))).elim
      · simp [hh, hxx]
  · have ha : σ (σ hub) = hub := by
      rcases hs (σ hub) hh with ha | ha
      · exact ha
      · exact (hh (σ.injective ha)).elim
    by_cases hx : x = hub
    · subst x; simp
    by_cases hxa : x = σ hub
    · subst x; simpa using ha
    have hxx : σ x = x := by
      rcases hs x hx with hxh | hxx
      · exact (hxa (σ.injective (hxh.trans ha.symm))).elim
      · exact hxx
    simp [Equiv.swap_apply_of_ne_of_ne hx hxa, hxx]

private theorem hub_swap_weight {n : Type*} [DecidableEq n] [Fintype n]
    (hub a : n) (c : ℂ) :
    (∏ i, hubMatrix hub c (Equiv.swap hub a i) i) = if a = hub then c else 1 := by
  by_cases ha : a = hub
  · subst a
    simp only [Equiv.swap_self, Equiv.refl_apply, ite_true]
    calc
      (∏ x, hubMatrix hub c x x) = hubMatrix hub c hub hub := by
        apply Finset.prod_eq_single hub
        · intro b _ hb
          simp [hubMatrix, hb]
        · simp
      _ = _ := by simp [hubMatrix]
  · have he (i : n) : hubMatrix hub c (Equiv.swap hub a i) i = 1 := by
      by_cases hi : i = hub
      · subst i; simp [hubMatrix, ha]
      by_cases hia : i = a
      · subst i; simp [hubMatrix, ha]
      simp [Equiv.swap_apply_of_ne_of_ne hi hia, hubMatrix, hi]
    simp [he, ha]

/-- Exact permanent formula for arbitrary arrowhead hub weight. -/
theorem permanent_hubMatrix {n : Type*} [DecidableEq n] [Fintype n]
    (hub : n) (c : ℂ) : (hubMatrix hub c).permanent = c + Fintype.card n - 1 := by
  have hinj : Function.Injective (fun a : n => Equiv.swap hub a) := by
    intro a b hab
    have := congrArg (fun σ : Equiv.Perm n => σ hub) hab
    simpa using this
  unfold Matrix.permanent
  have hr : (∑ σ : Equiv.Perm n, ∏ i, hubMatrix hub c (σ i) i) =
      ∑ a : n, ∏ i, hubMatrix hub c (Equiv.swap hub a i) i := by
    let f : Equiv.Perm n → ℂ := fun σ => ∏ i, hubMatrix hub c (σ i) i
    change (∑ σ, f σ) = ∑ a, f (Equiv.swap hub a)
    rw [← Finset.sum_image (fun a _ b _ hab => hinj hab)]
    apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro σ _ hσ
    by_contra hn
    exact hσ (Finset.mem_image.mpr ⟨σ hub, Finset.mem_univ _, (hub_supported hub c σ hn).symm⟩)
  rw [hr]
  simp_rw [hub_swap_weight]
  have he (a : n) : (if a = hub then c else (1 : ℂ)) =
      1 + if a = hub then c - 1 else 0 := by split_ifs <;> ring
  simp_rw [he]
  simp [Finset.sum_add_distrib]
  ring

/-- Delete a named row and column, retaining a common `Fin l` indexing of their complements. -/
def cofactor (l : ℕ) (a b : Option (Fin l)) : ℂ :=
  ((arrowhead l).submatrix
    (fun i => Equiv.swap none a (some i))
    (fun j => Equiv.swap none b (some j))).permanent

@[simp] theorem cofactor_hub_hub (l : ℕ) : cofactor l none none = 1 := by
  simpa [cofactor] using permanent_leaf_submatrix l

@[simp] theorem cofactor_leaf_diagonal (l : ℕ) (a : Fin l) :
    cofactor l (some a) (some a) = -1 := by
  have he : (arrowhead l).submatrix
      (fun i => Equiv.swap none (some a) (some i))
      (fun j => Equiv.swap none (some a) (some j)) = hubMatrix a (-(l : ℂ)) := by
    ext i j
    by_cases hi : i = a <;> by_cases hj : j = a <;>
      simp [Matrix.submatrix, hi, hj, Equiv.swap_apply_of_ne_of_ne, arrowhead, hubMatrix]
  unfold cofactor
  rw [he, permanent_hubMatrix]
  simp

private theorem perm_eq_one_of_fixed_except {n : Type*} [DecidableEq n]
    (σ : Equiv.Perm n) (b : n) (h : ∀ j, j ≠ b → σ j = j) : σ = 1 := by
  have hb : σ b = b := by
    by_contra hn
    exact hn (σ.injective (h (σ b) hn))
  ext j
  by_cases hj : j = b
  · subst j; exact hb
  · exact h j hj

private theorem permanent_of_unique_support {n : Type*} [DecidableEq n] [Fintype n]
    (M : Matrix n n ℂ) (hd : ∀ i, M i i = 1)
    (hs : ∀ σ : Equiv.Perm n, (∏ i, M (σ i) i) ≠ 0 → σ = 1) : M.permanent = 1 := by
  unfold Matrix.permanent
  rw [Finset.sum_eq_single (1 : Equiv.Perm n)]
  · simp [hd]
  · intro σ _ hσ
    by_contra hn
    exact hσ (hs σ hn)
  · simp

@[simp] theorem cofactor_hub_leaf (l : ℕ) (b : Fin l) :
    cofactor l none (some b) = 1 := by
  unfold cofactor
  apply permanent_of_unique_support
  · intro i
    by_cases hi : i = b <;>
      simp [Matrix.submatrix, hi, Equiv.swap_apply_of_ne_of_ne, arrowhead]
  · intro σ hn
    apply perm_eq_one_of_fixed_except σ b
    intro j hj
    by_contra hσ
    apply hn
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [Matrix.submatrix, Equiv.swap_apply_of_ne_of_ne, hj, hσ, arrowhead]

theorem cofactor_symm (l : ℕ) (a b : Option (Fin l)) : cofactor l a b = cofactor l b a := by
  have hs : (arrowhead l).transpose = arrowhead l := by
    ext i j
    cases i <;> cases j <;> simp [arrowhead, Matrix.transpose_apply, eq_comm]
  unfold cofactor
  rw [← Matrix.permanent_transpose, Matrix.transpose_submatrix, hs]

@[simp] theorem cofactor_leaf_hub (l : ℕ) (a : Fin l) :
    cofactor l (some a) none = 1 := by
  rw [cofactor_symm, cofactor_hub_leaf]

/-- For two distinct leaves the deleted matrix has exactly one supported permutation. -/
theorem cofactor_distinct_leaves (l : ℕ) (a b : Fin l) (hab : a ≠ b) :
    cofactor l (some a) (some b) = 1 := by
  unfold cofactor
  apply permanent_of_unique_support
  · intro i
    by_cases hia : i = a <;> by_cases hib : i = b <;>
      simp_all [Matrix.submatrix, Equiv.swap_apply_of_ne_of_ne, arrowhead]
  · intro σ hn
    have he (j : Fin l) :
        arrowhead l (Equiv.swap none (some a) (some (σ j)))
          (Equiv.swap none (some b) (some j)) ≠ 0 := by
      intro hz
      apply hn
      exact Finset.prod_eq_zero (Finset.mem_univ j) hz
    have ha : σ a = a := by
      by_contra hσa
      have hz := he a
      simp [Equiv.swap_apply_of_ne_of_ne, hab, hσa, arrowhead] at hz
    apply perm_eq_one_of_fixed_except σ b
    intro j hj
    by_cases hja : j = a
    · subst j; exact ha
    have hσa : σ j ≠ a := by
      intro hh
      exact hja (σ.injective (hh.trans ha.symm))
    by_contra hσj
    have hz := he j
    simp [Equiv.swap_apply_of_ne_of_ne, hj, hσa, hσj, arrowhead] at hz

/-- Every permanent cofactor of the uniform sparse seed, including all small sizes. -/
theorem cofactor_formula (l : ℕ) (a b : Option (Fin l)) :
    cofactor l a b = match a, b with
      | none, _ => 1
      | _, none => 1
      | some i, some j => if i = j then -1 else 1 := by
  cases a with
  | none => cases b <;> simp
  | some a =>
    cases b with
    | none => simp
    | some b =>
      by_cases hab : a = b
      · subst b; simp
      · simp [cofactor_distinct_leaves l a b hab, hab]

end SparseSeed

#print axioms SparseSeed.permanent_hubMatrix
#print axioms SparseSeed.cofactor_formula
