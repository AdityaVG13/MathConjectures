import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Vaserstein.Statement

/-!
# The two cited results

The proof for `n ≥ 5` uses two published theorems, which are not proved here. They are stated
as `Prop`s for the field `F₂ = ZMod 2`, the only case used, and the main theorem takes them
as hypotheses.

* `KnuppelNielsen69`: F. Knüppel and K. Nielsen, *The extended covering number of SL_n is
  n + 1*, Linear Algebra Appl. 418 (2006) 634–656, Corollary 6.9.
* `BungerNielsen12`: F. Bünger and K. Nielsen, *A matrix-decomposition theorem for GL_n(K)*,
  Linear Algebra Appl. 298 (1999), Theorem 1.2.

Definitions follow the sources.

* A matrix `A ∈ K^{n×n}` is *cyclic* if some `v` makes `v, A v, …, A^{n-1} v` a basis of
  `K^n` (Knüppel–Nielsen, Section 2). Since there are `n` vectors, being a basis is the same
  as being linearly independent.
* The *minimum rank* `δ(A)` is `n` minus the number of invariant divisors of `A` different
  from `1`. Knüppel and Nielsen note in the proof of their Lemma 5.1 that
  `δ(A) = min {rank (A - λ) : λ ∈ L}` for an algebraic closure `L` of `K`; `minRank` is this
  formula.
-/

namespace Vaserstein

open Matrix Polynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- `A` is cyclic: some `v` makes `v, A v, …, A^(n-1) v` linearly independent. -/
def CyclicMatrix (A : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ v : Fin n → K, LinearIndependent K (fun i : Fin n => (A ^ (i : ℕ)) *ᵥ v)

/-- The minimum rank: the least rank of `A - λ` for `λ` in an algebraic closure of `K`. -/
noncomputable def minRank (A : Matrix (Fin n) (Fin n) K) : ℕ :=
  ⨅ μ : AlgebraicClosure K,
    (A.map (algebraMap K (AlgebraicClosure K)) - Matrix.scalar (Fin n) μ).rank

/-- **Knüppel–Nielsen, Corollary 6.9**, for `K = F₂`: if `n ≥ 3`, `n ≠ 4`, and `C₁, …, Cₘ`
are non-central conjugacy classes of `SL_n(F₂)` whose minimum ranks sum to at least `n - 1`,
then `C₁ ⋯ Cₘ` contains a cyclic matrix. Each class is given by a representative. -/
def KnuppelNielsen69 : Prop :=
  ∀ n : ℕ, 3 ≤ n → n ≠ 4 → ∀ (m : ℕ) (C : Fin m → SpecialLinearGroup (Fin n) (ZMod 2)),
    (∀ i, C i ∉ Subgroup.center (SpecialLinearGroup (Fin n) (ZMod 2))) →
    n - 1 ≤ ∑ i, minRank (C i : Matrix (Fin n) (Fin n) (ZMod 2)) →
    ∃ c : Fin m → SpecialLinearGroup (Fin n) (ZMod 2), (∀ i, IsConj (C i) (c i)) ∧
      CyclicMatrix (((List.ofFn c).prod : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2))

/-- **Bünger–Nielsen, Theorem 1.2**, for `K = F₂`: let `n ≥ 3`, let `M ∈ GL_n(F₂)` not be a
homothety, let `X` be a cyclic similarity class of `GL_n(F₂)` and let `q` be monic of degree
`n - 1` with `q(0) ≠ 0`. Then some similarity class `D` whose minimum polynomial is divisible
by `q` satisfies `M ∈ D X`. The class `X` is given by a representative. -/
def BungerNielsen12 : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ M : GL (Fin n) (ZMod 2),
    (∀ c : ZMod 2, (M : Matrix (Fin n) (Fin n) (ZMod 2)) ≠ Matrix.scalar (Fin n) c) →
    ∀ X : GL (Fin n) (ZMod 2), CyclicMatrix (X : Matrix (Fin n) (Fin n) (ZMod 2)) →
    ∀ q : (ZMod 2)[X], q.Monic → q.natDegree = n - 1 → q.coeff 0 ≠ 0 →
      ∃ d x : GL (Fin n) (ZMod 2), IsConj X x ∧
        q ∣ minpoly (ZMod 2) (d : Matrix (Fin n) (Fin n) (ZMod 2)) ∧ M = d * x

end Vaserstein
