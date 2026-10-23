# Kourovka Problem 16.21 over the field with two elements

L. Vaserstein asked, as Problem 16.21 of

> E. I. Khukhro, V. D. Mazurov (eds.), *Unsolved Problems in Group Theory. The Kourovka Notebook*,
> No. 21 (2026), [arXiv:1401.0300](https://arxiv.org/abs/1401.0300)

whether every non-central matrix in `SL_n(F)` is a product of `n` matrices similar to a given
non-central matrix. This folder answers the question affirmatively for the field `F₂`, with `n`
replaceable by any `k ≥ n`. The proof uses two published theorems, which it cites rather than
proves. Everything else is checked in Lean 4 with Mathlib.

The paper is [`paper/vaserstein-16-21.pdf`](paper/vaserstein-16-21.pdf) (source:
[`paper/vaserstein-16-21.tex`](paper/vaserstein-16-21.tex)).

## The question

> **16.21.** Given a non-central matrix `α ∈ SL_n(F)` over a field `F` for `n > 2`, is it true that
> every non-central matrix in `SL_n(F)` is a product of `n` matrices, each similar to `α`?
> *L. Vaserstein*

The 21st edition of the Notebook (2026) lists the problem as open. Over `F₂` every invertible
matrix has determinant `1`, so `SL_n(F₂) = GL_n(F₂)`, the centre is trivial, and "similar to `α`"
means "conjugate to `α`". The question becomes: is every nonidentity element of `GL_n(F₂)` a
product of `n` conjugates of any given nonidentity element?

## The result

**Theorem.** Assume Theorems A and B below. For `n ≥ 3`, nonidentity `α, g ∈ GL_n(F₂)` and
`k ≥ n`, the matrix `g` is a product of `k` conjugates of `α`.

The number `n` cannot be lowered in general: conjugates of a transvection `α` have
`rank(c - 1) = 1`, and `rank(xy - 1) ≤ rank(x - 1) + rank(y - 1)`, so a matrix `g` with `g - 1`
invertible needs at least `n` factors.

The proof shows more: if `n ≥ 5` and `α` has no J1 block (defined below), then
`2⌈(n - 1)/3⌉ + 1` factors, about `2n/3`, already suffice. So `n` is needed only for matrices close
to the identity.

The two cited results, in the special case `K = F₂` used here:

- **Theorem A.** F. Knüppel and K. Nielsen, *The extended covering number of SL_n is n + 1*,
  Linear Algebra Appl. 418 (2006) 634–656,
  [doi:10.1016/j.laa.2006.03.011](https://doi.org/10.1016/j.laa.2006.03.011), Corollary 6.9.
  For `n ≥ 3`, `n ≠ 4`, if non-central classes `C_1, …, C_m` of `SL_n(F₂)` have minimum ranks
  summing to at least `n - 1`, then `C_1 ⋯ C_m` contains a cyclic matrix.
- **Theorem B.** F. Bünger and K. Nielsen, *A matrix-decomposition theorem for GL_n(K)*,
  Linear Algebra Appl. 298 (1999) 39–50,
  [doi:10.1016/S0024-3795(99)00138-X](https://doi.org/10.1016/S0024-3795(99)00138-X),
  Theorem 1.2. For `n ≥ 3`, a non-homothety `M ∈ GL_n(F₂)`, a cyclic similarity class `X` and a
  monic `q` of degree `n - 1` with `q(0) ≠ 0`, there is a similarity class `D` whose minimal
  polynomial is divisible by `q` with `M ∈ D X`.

A matrix `A` is *cyclic* if `v, Av, …, A^(n-1) v` is a basis for some `v`. The *minimum rank*
`δ(A)` is the least rank of `A - λ` over `λ` in an algebraic closure.

## Proof sketch

Write `C` for the conjugacy class of `α` and `C^k` for the products of `k` elements of `C`. The
proof is a strong induction on `n`. Once every `g ≠ 1` is in `C^m`, the same holds for every
`k ≥ m`, because `α` is not central.

**`n = 3, 4`.** Computer-generated certificates: a conjugating matrix for every invertible matrix,
and for each pair of nonidentity class representatives an explicit product of `n` conjugates.
Lean checks them by kernel evaluation.

**`n ≥ 5`, `α` has a J1 block**, meaning `α` fixes a vector `v` and a covector `φ` with
`φ(v) = 1`, so `α = 1 ⊕ α'`.

- If `g` also has a J1 block, then `g = 1 ⊕ g'` and induction in dimension `n - 1` applies.
- Otherwise, *Lemma P* gives a conjugate `c` of `α` such that `g c⁻¹` has a J1 block, so
  `g ∈ C^(n-1) · C = C^n`. The conjugate is built by matching two frames of size 2, one adapted to
  `g` and one to `α`.
- Lemma P needs `g² + g + 1 ≠ 0` when `α` is an involution. In the remaining case `g` is a direct
  sum of order-3 blocks on planes, `n` is even, and induction in dimension `n - 2` applies.

**`n ≥ 5`, `α` has no J1 block.** Then `δ(α) ≥ 3`: for `λ = 1` a small `rank(α - 1)` would give a
J1 block, and for `λ ∉ F₂` squaring coordinates embeds the `λ`-eigenspace in the disjoint
`λ²`-eigenspace. Let `k = ⌈(n - 1)/3⌉`.

1. Theorem A applied to `k` copies of `C` gives a cyclic `D ∈ C^k`.
2. Let `r` be irreducible of degree `n - 1`. Theorem B gives `α = d' x'` with `x' ~ D⁻¹`, so
   `d' ∈ C^(k+1)`, and `g = d x` with `x ~ D`, where `r` divides the minimal polynomials of `d`
   and `d'`.
3. A matrix whose minimal polynomial is divisible by `r` has minimal polynomial `r(x + 1)`, so
   `d ~ d'`. Hence `g ∈ C^(2k+1)`, and `2k + 1 ≤ n`.

## How this was found

This work was produced almost entirely by an AI agent (Droid, by Factory), working under the
author's direction, while testing a new computational mathematics project (a programming
language for exact mathematical computation) on open problems. The agent carried out the
computations, found the argument, searched the literature, wrote the Lean formalization and
drafted the paper. The author chose the problem, set the scope and takes responsibility for the
result. No specialist has refereed the argument; the main evidence for its correctness is the Lean
check of every step outside the two cited theorems.

In outline: exhaustive computation settled `n = 3, 4` and random witness searches covered
`n = 5, 6`. The data suggested Lemma P and located its one exception. Matrices without a J1 block
resisted a direct argument until a literature search found the two cited theorems. Writing the
proof in Lean then simplified it: an earlier version split classes by minimum rank and needed a
third published result, and the final split by J1 blocks does not.

## Exact numbers for `n = 3, 4`

The paper gives, for every class of `GL_3(F₂)` and `GL_4(F₂)`, the least `m` such that every
nonidentity element is a product of `m` conjugates. Most classes need only 2. The bound `n` is
reached by the transvections and, in `GL_4(F₂)`, by `ω ⊕ ω`, the fixed-point-free element of
order 3. These numbers come from a separate exhaustive computation and are not formalized; Lean
checks the bound `m ≤ n`.
## What the Lean proof checks

The main results are in [`Vaserstein/Main.lean`](Vaserstein/Main.lean):

| Theorem | Statement |
| --- | --- |
| `Vaserstein.question` | `KnuppelNielsen69 → BungerNielsen12 → Question (ZMod 2)` |
| `Vaserstein.questionFrom` | the same with any number `k ≥ n` of factors |
| `Vaserstein.covers` | the induction: every nonidentity element of `GL(W)` over `F₂`, `dim W = n ≥ 3`, is a product of `k ≥ n` conjugates of any nonidentity element |
| `Vaserstein.covers_three`, `covers_four` | the cases `n = 3` and `n = 4`, with no hypotheses |

`Question F` is defined from the wording of the problem in
[`Statement.lean`](Vaserstein/Statement.lean), using `SpecialLinearGroup`, its centre, and
similarity by an invertible matrix. The two cited theorems are stated as `Prop`s in
[`Cited.lean`](Vaserstein/Cited.lean), with cyclicity and minimum rank defined from the sources,
and `question` takes them as hypotheses.

| File | Contents |
| --- | --- |
| `Statement.lean` | The question, defined from its wording |
| `Cited.lean` | Theorems A and B, as hypotheses |
| `Basic.lean` | Products of conjugates in a group; passing from `n` to `k ≥ n` factors |
| `Linear.lean` | Direct sums, restrictions and frames in `GL(V)` |
| `Bits.lean`, `Certificates.lean`, `Data/` | The certificate checker and the data for `n = 3, 4` |
| `Small.lean` | The cases `n = 3` and `n = 4` |
| `LemmaP.lean` | J1 blocks and Lemma P |
| `Exception.lean` | The case Lemma P excludes |
| `CaseC.lean` | `α` with a J1 block |
| `MinRank.lean` | `δ(α) ≥ 3` when `α` has no J1 block |
| `ClassN.lean` | Matrices whose minimal polynomial is divisible by `r` are conjugate |
| `Cyclic.lean` | `α` without a J1 block, using Theorems A and B |
| `Main.lean` | The induction and the transfer to `SL_n(ZMod 2)` |

The proof uses no `sorry`, no new axioms and no `native_decide`. The certificates are checked
with `decide +kernel`. Every main theorem depends only on Lean's standard axioms `propext`,
`Classical.choice` and `Quot.sound`; Theorems A and B enter only as hypotheses.

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain and the Mathlib revision are
pinned in `lean-toolchain` and `lake-manifest.json`.

From this folder:

```
lake exe cache get
lake build
```

The build prints the axioms each main theorem depends on.

## Prior work

- Knüppel and Nielsen (2006), cited above, determine the extended covering number of
  `SL_n(K)`: the least `k` with `1 ∈ C_1 ⋯ C_k` for all non-central classes `C_i`, when `n` and
  `K` are not too small. The proof here uses their Corollary 6.9.
- F. Knüppel, *Products of similar matrices*, Linear Algebra Appl. 233 (1996) 99–108, studies the
  least `k` such that every element of `SL(V)` is a product of at most `k` elements of a given
  class.
- A. Lev, *Products of cyclic similarity classes in the groups GL_n(F)*, Linear Algebra Appl. 202
  (1994) 235–266, treats products of two cyclic classes when `|F| ≥ 4`.
- In October 2026 we found no solution of Problem 16.21 for `F₂` in the Notebook or in a web
  search. We do not know whether the problem has been settled for other
  fields, and make no claim about them. If you know of a solution, please open an issue.
