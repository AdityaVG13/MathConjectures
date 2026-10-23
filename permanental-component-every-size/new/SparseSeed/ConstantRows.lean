import SparseSeed.Cofactors
import Mathlib.GroupTheory.Perm.Option

namespace SparseSeed
open Finset Equiv

/-- The identity matrix with the rows in `s` replaced by rowwise constants. -/
def constantRows {n : Type*} [DecidableEq n] (s : Finset n) (c : n → ℂ) : Matrix n n ℂ :=
  fun i j => if i ∈ s then c i else if i = j then 1 else 0

/-- A uniform counting identity: only permutations of the replaced rows contribute. -/
theorem permanent_constantRows {n : Type*} [DecidableEq n] [Fintype n]
    (s : Finset n) (c : n → ℂ) :
    (constantRows s c).permanent = (s.card.factorial : ℂ) * ∏ i ∈ s, c i := by
  have hzero (σ : Equiv.Perm n) (hσ : σ ∉ permsOfFinset s) :
      (∏ i, constantRows s c (σ i) i) = 0 := by
    by_contra hn
    apply hσ
    apply mem_perms_of_finset_iff.mpr
    intro x hx
    by_contra hxs
    have hxinv : x ≠ σ.symm x := by
      intro hh
      apply hx
      have := congrArg σ hh
      simpa using this
    apply hn
    apply Finset.prod_eq_zero (Finset.mem_univ (σ.symm x))
    simp [constantRows, hxs, hxinv]
  have hweight (σ : Equiv.Perm n) (hσ : σ ∈ permsOfFinset s) :
      (∏ i, constantRows s c (σ i) i) = ∏ i ∈ s, c i := by
    have hfix (i : n) (hi : i ∉ s) : σ i = i := by
      by_contra hn
      exact hi (mem_perms_of_finset_iff.mp hσ hn)
    have he (i : n) : constantRows s c (σ i) i = if σ i ∈ s then c (σ i) else 1 := by
      by_cases hi : σ i ∈ s
      · simp [constantRows, hi]
      · have hh : σ i = i := σ.injective (hfix (σ i) hi)
        simp [constantRows, hh]
    simp_rw [he]
    calc
      (∏ i, if σ i ∈ s then c (σ i) else 1) = ∏ i, if i ∈ s then c i else 1 :=
        Fintype.prod_equiv σ _ _ (fun _ => rfl)
      _ = ∏ i ∈ s, c i := Finset.prod_ite_mem_eq s c
  unfold Matrix.permanent
  rw [← Finset.sum_subset (Finset.subset_univ (permsOfFinset s)) (fun σ _ hσ => hzero σ hσ)]
  rw [Finset.sum_congr rfl hweight]
  simp [card_perms_of_finset, nsmul_eq_mul]

/-- Laplace expansion along the hub column, with swap-indexed deletions. -/
theorem permanent_option_hub_column {n : Type*} [DecidableEq n] [Fintype n]
    (A : Matrix (Option n) (Option n) ℂ) :
    A.permanent = ∑ a : Option n, A a none *
      (A.submatrix (fun i => Equiv.swap none a (some i)) some).permanent := by
  rw [Matrix.permanent, Finset.univ_perm_option, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  simp [Matrix.permanent, Fintype.prod_option, Finset.mul_sum,
    Matrix.submatrix, Equiv.Perm.decomposeOption, Equiv.Perm.mul_apply]

end SparseSeed

#print axioms SparseSeed.permanent_constantRows
#print axioms SparseSeed.permanent_option_hub_column
