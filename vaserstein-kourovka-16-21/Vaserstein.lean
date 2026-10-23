import Vaserstein.Main

/-!
# Kourovka Problem 16.21 over the field with two elements

L. Vaserstein asked (*The Kourovka Notebook*, Problem 16.21): given a non-central matrix
`α ∈ SL_n(F)` over a field `F` for `n > 2`, is every non-central matrix in `SL_n(F)` a product of
`n` matrices, each similar to `α`?

`Vaserstein.question` answers this in the affirmative for `F = ZMod 2`, and
`Vaserstein.questionFrom` gives the stronger form with any number `k ≥ n` of factors. Both take
two published theorems as hypotheses, stated in `Vaserstein.Cited`: Corollary 6.9 of
Knüppel–Nielsen (2006) and Theorem 1.2 of Bünger–Nielsen (1999).

* `Vaserstein.Statement` defines the question from its wording.
* `Vaserstein.Small` checks `n = 3` and `n = 4` by kernel computation.
* `Vaserstein.CaseC` treats a matrix with a J1 block (a fixed vector that splits off), using
  Lemma P (`Vaserstein.LemmaP`) and its exception (`Vaserstein.Exception`).
* `Vaserstein.Cyclic` treats all other matrices, using `Vaserstein.MinRank` and
  `Vaserstein.ClassN`.
* `Vaserstein.Main` runs the induction on `n`.

The `#print axioms` lines below report the axioms each main theorem depends on.
-/

#print axioms Vaserstein.question
#print axioms Vaserstein.questionFrom
#print axioms Vaserstein.covers
#print axioms Vaserstein.covers_three
#print axioms Vaserstein.covers_four
