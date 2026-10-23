import SparseSeed.Arrowhead

namespace AmbientRestriction
open Finset Equiv
set_option backward.isDefEq.respectTransparency false

/-- A row-oriented version of the permanent sum. -/
theorem permanent_sum_rows {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    M.permanent = ∑ σ : Equiv.Perm n, ∏ i, M i (σ i) := by
  rw [← Matrix.permanent_transpose]
  rfl

/-- A permanent vanishes when a supported permutation would have to preserve partitions
with different cardinalities. -/
theorem permanent_zero_of_partition {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (f g : n → ℕ)
    (hzero : ∀ i j, f i ≠ g j → M i j = 0)
    (hcard : (∑ i, f i) ≠ ∑ j, g j) : M.permanent = 0 := by
  rw [permanent_sum_rows]
  apply Finset.sum_eq_zero
  intro σ _
  by_contra hn
  have hfg (i : n) : f i = g (σ i) := by
    by_contra hh
    exact hn (Finset.prod_eq_zero (Finset.mem_univ i) (hzero i (σ i) hh))
  apply hcard
  calc
    (∑ i, f i) = ∑ i, g (σ i) := Finset.sum_congr rfl (fun i _ => hfg i)
    _ = ∑ j, g j := Fintype.sum_equiv σ _ _ (fun _ => rfl)

/-- Arbitrarily chosen left/right summands in the three top rows. -/
def splitTop {n : Type*} (s : Finset (Fin 3))
    (L R : Matrix (Fin 3) (Fin 3 ⊕ n) ℂ) (D : Matrix n (Fin 3 ⊕ n) ℂ) :
    Matrix (Fin 3 ⊕ n) (Fin 3 ⊕ n) ℂ
  | Sum.inl i, j => if i ∈ s then L i j else R i j
  | Sum.inr i, j => D i j

def addTop {n : Type*} (L R : Matrix (Fin 3) (Fin 3 ⊕ n) ℂ)
    (D : Matrix n (Fin 3 ⊕ n) ℂ) : Matrix (Fin 3 ⊕ n) (Fin 3 ⊕ n) ℂ
  | Sum.inl i, j => L i j + R i j
  | Sum.inr i, j => D i j

/-- Exact three-row multilinearity, with all eight terms retained. -/
theorem permanent_addTop {n : Type*} [Fintype n] [DecidableEq n]
    (L R : Matrix (Fin 3) (Fin 3 ⊕ n) ℂ) (D : Matrix n (Fin 3 ⊕ n) ℂ) :
    (addTop L R D).permanent =
      (splitTop ∅ L R D).permanent +
      (splitTop {0} L R D).permanent + (splitTop {1} L R D).permanent +
      (splitTop {2} L R D).permanent + (splitTop {0, 1} L R D).permanent +
      (splitTop {0, 2} L R D).permanent + (splitTop {1, 2} L R D).permanent +
      (splitTop {0, 1, 2} L R D).permanent := by
  simp_rw [permanent_sum_rows]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  simp [Fintype.prod_sum_type, Fin.prod_univ_succ, addTop, splitTop]
  ring

end AmbientRestriction

#print axioms AmbientRestriction.permanent_zero_of_partition
#print axioms AmbientRestriction.permanent_addTop
