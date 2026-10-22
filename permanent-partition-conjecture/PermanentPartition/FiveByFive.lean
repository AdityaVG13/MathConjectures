import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import PermanentPartition.Criterion

/-!
# The 5 × 5 counterexample

`A` is the matrix

```
1  1  1  1  0
1  0 -1  0  0
1 -1  1  1  0
2  0  2  1  1
2  0  2  1 -1
```

All 25 of its `4 × 4` permanents vanish, so `A ∈ Sing(P)`. Every row and every column has a
nonzero entry, and every two rows and every two columns have a nonzero `2 × 2` permanent. In a
partition of five rows (or columns) one part has at most two elements, so no partition has both
parts vanishing.

Unlike `H`, this matrix is invertible (`A_det`), so the failure of the conjecture is not tied to
a block of zeros.
-/

namespace PermanentPartition

open Matrix

/-- The `5 × 5` witness. -/
def A : Matrix (Fin 5) (Fin 5) ℂ :=
  !![1, 1, 1, 1, 0;
     1, 0, -1, 0, 0;
     1, -1, 1, 1, 0;
     2, 0, 2, 1, 1;
     2, 0, 2, 1, -1]

theorem A_det : A.det = -8 := by
  simp [det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, A]
  norm_num

theorem A_minors : ∀ r c : Fin 5, (A.submatrix r.succAbove c.succAbove).permanent = 0 := by
  intro r c
  fin_cases r <;> fin_cases c <;>
    norm_num [permanent_succ_column_zero, Fin.sum_univ_succ, permanent_unique, Fin.succAbove, A]

theorem A_isSingular : IsSingular A :=
  (isSingular_iff A).mpr A_minors

theorem A_rows_one : ∀ i, ∃ j, A i j ≠ 0 := by
  intro i
  fin_cases i <;> exact ⟨0, by norm_num [A]⟩

section

-- In each `first` alternative, `done` makes a choice of columns that leaves a goal fail, so that
-- the next choice is tried. The linter reports it as unused wherever the choice succeeds.
set_option linter.unusedTactic false

theorem A_columns_one : ∀ i, ∃ j, Aᵀ i j ≠ 0 := by
  intro i
  fin_cases i <;> first
    | (refine ⟨0, ?_⟩; norm_num [A]; done)
    | (refine ⟨3, ?_⟩; norm_num [A]; done)

theorem A_rows_two :
    ∀ i j, i ≠ j → ∃ c d, c ≠ d ∧ A i c * A j d + A i d * A j c ≠ 0 := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl h
    | (refine ⟨0, 1, by decide, ?_⟩; norm_num [A]; done)
    | (refine ⟨0, 2, by decide, ?_⟩; norm_num [A]; done)
    | (refine ⟨0, 3, by decide, ?_⟩; norm_num [A]; done)

theorem A_columns_two :
    ∀ i j, i ≠ j → ∃ c d, c ≠ d ∧ Aᵀ i c * Aᵀ j d + Aᵀ i d * Aᵀ j c ≠ 0 := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl h
    | (refine ⟨0, 1, by decide, ?_⟩; norm_num [A]; done)
    | (refine ⟨0, 2, by decide, ?_⟩; norm_num [A]; done)
    | (refine ⟨0, 3, by decide, ?_⟩; norm_num [A]; done)

end

theorem A_no_partition_oriented (column : Bool) (S : Finset (Fin 5)) (hS : S.Nonempty)
    (hU : S ≠ Finset.univ) :
    ¬ (Vanishes (orient column A) S ∧ Vanishes (orient column A) Sᶜ) := by
  cases column
  · exact no_partition_of_small A (not_vanishes_of_card_le_two A A_rows_one A_rows_two) S hS hU
  · exact no_partition_of_small Aᵀ
      (not_vanishes_of_card_le_two Aᵀ A_columns_one A_columns_two) S hS hU

end PermanentPartition
