import Mathlib.LinearAlgebra.Matrix.Notation
import PermanentPartition.Criterion

/-!
# The 4 × 4 counterexample

`H` has a `3 × 3` block of zeros and ones everywhere else:

```
0 0 0 1
0 0 0 1
0 0 0 1
1 1 1 1
```

Every `3 × 3` permanent of `H` vanishes: any three rows include two of the first three rows, and
both of those rows have their only nonzero entry in the last column, which a single permutation
term cannot use twice. So `H ∈ Sing(P)`.

No partition of the rows has both parts vanishing. A part with one row has a nonzero entry. In a
partition into two pairs, the pair containing the last row has the nonzero `2 × 2` permanent on
the first and last columns. `H` is symmetric, so the same holds for columns.

The support of `H` is that of a type (1) prime in Kirkup's classification of the minimal primes
of the ideal of `3 × 3` subpermanents of a `4 × 4` matrix (G. A. Kirkup, *Minimal primes over
permanental ideals*, Trans. Amer. Math. Soc. 360 (2008), §§8–9).
-/

namespace PermanentPartition

open Matrix

/-- The `4 × 4` witness. -/
def H : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 1;
     0, 0, 0, 1;
     0, 0, 0, 1;
     1, 1, 1, 1]

theorem H_transpose : Hᵀ = H := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem H_minors : ∀ r c : Fin 4, (H.submatrix r.succAbove c.succAbove).permanent = 0 := by
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [permanent_succ_column_zero, Fin.sum_univ_succ, permanent_unique, Fin.succAbove, H]

theorem H_isSingular : IsSingular H :=
  (isSingular_iff H).mpr H_minors

/-- A pair of rows that contains the last row does not vanish. -/
theorem H_not_vanishes_pair_last (y : Fin 4) (hy : y ≠ 3) : ¬ Vanishes H {3, y} := by
  refine not_vanishes_pair H (c := 3) (d := 0) (Ne.symm hy) (by decide) ?_
  fin_cases y <;> simp_all [H]

theorem H_not_vanishes_of_card_two (T : Finset (Fin 4)) (hT : T.card = 2) (h3 : 3 ∈ T) :
    ¬ Vanishes H T := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hT
  rcases Finset.mem_insert.mp h3 with h | h
  · subst h
    exact H_not_vanishes_pair_last y (Ne.symm hxy)
  · rw [Finset.mem_singleton] at h
    subst h
    rw [Finset.pair_comm]
    exact H_not_vanishes_pair_last x hxy

theorem H_no_partition (S : Finset (Fin 4)) (hS : S.Nonempty) (hU : S ≠ Finset.univ) :
    ¬ (Vanishes H S ∧ Vanishes H Sᶜ) := by
  rintro ⟨h1, h2⟩
  have hS' : Sᶜ.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr fun he => hU ((Finset.compl_eq_empty_iff S).mp he)
  have hcard : S.card + Sᶜ.card = 4 := by simp
  have hpos := Finset.card_pos.mpr hS
  have hpos' := Finset.card_pos.mpr hS'
  have hlast : ∀ i : Fin 4, H i 3 ≠ 0 := by
    intro i
    fin_cases i <;> simp [H]
  by_cases hone : S.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hone
    exact not_vanishes_singleton H (hlast i) h1
  by_cases hone' : Sᶜ.card = 1
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone'
    rw [hi] at h2
    exact not_vanishes_singleton H (hlast i) h2
  by_cases h3 : (3 : Fin 4) ∈ S
  · exact H_not_vanishes_of_card_two S (by omega) h3 h1
  · exact H_not_vanishes_of_card_two Sᶜ (by omega) (Finset.mem_compl.mpr h3) h2

theorem H_no_partition_oriented (column : Bool) (S : Finset (Fin 4)) (hS : S.Nonempty)
    (hU : S ≠ Finset.univ) :
    ¬ (Vanishes (orient column H) S ∧ Vanishes (orient column H) Sᶜ) := by
  cases column
  · exact H_no_partition S hS hU
  · simpa [orient, H_transpose] using H_no_partition S hS hU

end PermanentPartition
