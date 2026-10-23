import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.Subgroup.Center

/-!
# The statement of Kourovka Problem 16.21

Reference: *The Kourovka Notebook. Unsolved Problems in Group Theory*, edited by E. I. Khukhro
and V. D. Mazurov, Problem 16.21 (L. Vaserstein):

  Given a non-central matrix `α ∈ SL_n(F)` over a field `F` for `n > 2`, is it true that every
  non-central matrix in `SL_n(F)` is a product of `n` matrices, each similar to `α`?

This file defines the question directly from that wording.

* `Similar A B` says that `B = P A P⁻¹` for some invertible `P`, that is, `B` is similar to `A`
  in the usual sense of linear algebra. A matrix similar to `α` has determinant `1`, so it lies
  in `SL_n(F)`; the factors are therefore taken as plain matrices.
* `IsProductOfSimilar k α β` says that `β` is a product of `k` matrices, each similar to `α`.
* `Question F` is the question for the field `F`: a positive answer for every `n > 2`.
* `QuestionFrom F` is the stronger statement with `n` replaced by any `k ≥ n`.

The question is asked for an arbitrary field. The results of this project concern `F = ZMod 2`.
-/

namespace Vaserstein

open Matrix

variable {F : Type*} [Field F] {n : ℕ}

/-- `B` is similar to `A`: `B = P A P⁻¹` for an invertible matrix `P`. -/
def Similar (A B : Matrix (Fin n) (Fin n) F) : Prop :=
  ∃ P : GL (Fin n) F, B = (P : Matrix (Fin n) (Fin n) F) * A * ((P⁻¹ : GL (Fin n) F) :
    Matrix (Fin n) (Fin n) F)

/-- `β` is a product `f 0 * f 1 * ⋯ * f (k - 1)` of `k` matrices, each similar to `α`. -/
def IsProductOfSimilar (k : ℕ) (α β : Matrix (Fin n) (Fin n) F) : Prop :=
  ∃ f : Fin k → Matrix (Fin n) (Fin n) F, (∀ i, Similar α (f i)) ∧ (List.ofFn f).prod = β

/-- Kourovka Problem 16.21 for the field `F`: for every `n > 2` and every non-central
`α ∈ SL_n(F)`, every non-central `β ∈ SL_n(F)` is a product of `n` matrices similar to `α`. -/
def Question (F : Type*) [Field F] : Prop :=
  ∀ n : ℕ, 2 < n → ∀ α β : SpecialLinearGroup (Fin n) F,
    α ∉ Subgroup.center (SpecialLinearGroup (Fin n) F) →
    β ∉ Subgroup.center (SpecialLinearGroup (Fin n) F) →
    IsProductOfSimilar n (α : Matrix (Fin n) (Fin n) F) (β : Matrix (Fin n) (Fin n) F)

/-- The stronger form: the same holds with `n` factors replaced by any number `k ≥ n`. -/
def QuestionFrom (F : Type*) [Field F] : Prop :=
  ∀ n : ℕ, 2 < n → ∀ k : ℕ, n ≤ k → ∀ α β : SpecialLinearGroup (Fin n) F,
    α ∉ Subgroup.center (SpecialLinearGroup (Fin n) F) →
    β ∉ Subgroup.center (SpecialLinearGroup (Fin n) F) →
    IsProductOfSimilar k (α : Matrix (Fin n) (Fin n) F) (β : Matrix (Fin n) (Fin n) F)

theorem question_of_questionFrom (h : QuestionFrom F) : Question F :=
  fun n hn α β hα hβ => h n hn n le_rfl α β hα hβ

end Vaserstein
