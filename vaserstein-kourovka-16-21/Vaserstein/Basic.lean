import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Tactic.Group

/-!
# Products of conjugates in a group

For an element `a` of a group, `conjugatesOf a ^ k` is the set of products of `k` conjugates of
`a`. This file collects the facts about these sets that do not depend on matrices: they are
closed under conjugation, they only depend on the conjugacy class of `a`, and once every
nonidentity element is a product of `m` conjugates, the same holds for every `k ≥ m`.
-/

namespace Vaserstein

open Pointwise

variable {G : Type*} [Group G]

theorem mul_mem_pow_succ {s : Set G} {k : ℕ} {u v : G} (hu : u ∈ s ^ k) (hv : v ∈ s) :
    u * v ∈ s ^ (k + 1) := by
  rw [pow_succ]
  exact Set.mul_mem_mul hu hv

theorem conj_mem_conjugatesOf {a y : G} (x : G) (hy : y ∈ conjugatesOf a) :
    x * y * x⁻¹ ∈ conjugatesOf a :=
  (hy : IsConj a y).trans (isConj_iff.2 ⟨x, rfl⟩)

theorem conj_mem_conjugatesOf_pow {a y : G} (x : G) {k : ℕ} (hy : y ∈ conjugatesOf a ^ k) :
    x * y * x⁻¹ ∈ conjugatesOf a ^ k := by
  induction k generalizing y with
  | zero =>
    rw [pow_zero, Set.mem_one] at hy ⊢
    simp [hy]
  | succ k ih =>
    rw [pow_succ] at hy ⊢
    obtain ⟨u, hu, v, hv, rfl⟩ := hy
    exact ⟨x * u * x⁻¹, ih hu, x * v * x⁻¹, conj_mem_conjugatesOf x hv, by
      show x * u * x⁻¹ * (x * v * x⁻¹) = x * (u * v) * x⁻¹
      group⟩

theorem mem_conjugatesOf_pow_of_isConj {a b g : G} {k : ℕ} (hab : IsConj a b)
    (hg : g ∈ conjugatesOf b ^ k) : g ∈ conjugatesOf a ^ k := by
  rwa [isConj_iff_conjugatesOf_eq.1 hab]

/-- Covering is inherited by every larger number of factors, provided `a` is not central. -/
theorem covers_of_le {a : G} (hna : ∃ x, x * a * x⁻¹ ≠ a) {m k : ℕ} (hmk : m ≤ k)
    (h : ∀ g : G, g ≠ 1 → g ∈ conjugatesOf a ^ m) : ∀ g : G, g ≠ 1 → g ∈ conjugatesOf a ^ k := by
  intro g hg
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hmk
  rcases j with _ | j
  · simpa using h g hg
  obtain ⟨x, hx⟩ := hna
  have ha : a ∈ conjugatesOf a := IsConj.refl a
  have h1 : a ^ (j + 1) ∈ conjugatesOf a ^ (j + 1) := Set.pow_mem_pow ha
  have h2 : (x * a * x⁻¹) * a ^ j ∈ conjugatesOf a ^ (j + 1) := by
    rw [pow_succ']
    exact Set.mul_mem_mul (conj_mem_conjugatesOf x ha) (Set.pow_mem_pow ha)
  have : ∃ u ∈ conjugatesOf a ^ (j + 1), u ≠ g := by
    by_cases hg1 : a ^ (j + 1) = g
    · refine ⟨_, h2, fun h3 => hx ?_⟩
      rw [← hg1, pow_succ'] at h3
      exact mul_right_cancel h3
    · exact ⟨_, h1, hg1⟩
  obtain ⟨u, hu, hug⟩ := this
  have hv : u⁻¹ * g ≠ 1 := fun h3 => hug (inv_mul_eq_one.1 h3)
  rw [pow_add]
  exact ⟨u, hu, u⁻¹ * g, h _ hv, by
    show u * (u⁻¹ * g) = g
    group⟩

theorem mem_pow_add {s : Set G} {j k : ℕ} {u v : G} (hu : u ∈ s ^ j) (hv : v ∈ s ^ k) :
    u * v ∈ s ^ (j + k) := by
  rw [pow_add]
  exact Set.mul_mem_mul hu hv

theorem map_mem_conjugatesOf_pow {H : Type*} [Group H] (f : G →* H) {a g : G} {k : ℕ}
    (hg : g ∈ conjugatesOf a ^ k) : f g ∈ conjugatesOf (f a) ^ k := by
  induction k generalizing g with
  | zero =>
    rw [pow_zero, Set.mem_one] at hg ⊢
    simp [hg]
  | succ k ih =>
    rw [pow_succ] at hg ⊢
    obtain ⟨u, hu, v, hv, rfl⟩ := hg
    exact ⟨f u, ih hu, f v, f.map_isConj hv, (map_mul f u v).symm⟩

theorem mem_conjugatesOf_pow_iff_of_mulEquiv {H : Type*} [Group H] (e : G ≃* H) {a g : G}
    {k : ℕ} : e g ∈ conjugatesOf (e a) ^ k ↔ g ∈ conjugatesOf a ^ k := by
  refine ⟨fun h => ?_, fun h => map_mem_conjugatesOf_pow e.toMonoidHom h⟩
  simpa using map_mem_conjugatesOf_pow e.symm.toMonoidHom h

/-- Products of conjugates in a direct product, factor by factor. -/
theorem prod_mem_conjugatesOf_pow {H : Type*} [Group H] {a x : G} {b y : H} {k : ℕ}
    (hx : x ∈ conjugatesOf a ^ k) (hy : y ∈ conjugatesOf b ^ k) :
    (x, y) ∈ conjugatesOf (a, b) ^ k := by
  induction k generalizing x y with
  | zero =>
    rw [pow_zero, Set.mem_one] at hx hy ⊢
    simp [hx, hy]
  | succ k ih =>
    rw [pow_succ] at hx hy ⊢
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    obtain ⟨u', hu', v', hv', rfl⟩ := hy
    refine ⟨(u, u'), ih hu hu', (v, v'), ?_, rfl⟩
    obtain ⟨c, hc⟩ := isConj_iff.1 hv
    obtain ⟨c', hc'⟩ := isConj_iff.1 hv'
    exact isConj_iff.2 ⟨(c, c'), by simp [hc, hc']⟩

/-- For an involution `a`, a product of `k` conjugates is also a product of `k + 2`. -/
theorem mem_pow_add_two {a g : G} (ha : a * a = 1) {k : ℕ} (hg : g ∈ conjugatesOf a ^ k) :
    g ∈ conjugatesOf a ^ (k + 2) := by
  have h1 : (1 : G) ∈ conjugatesOf a ^ 2 := by
    rw [pow_two]
    exact ⟨a, IsConj.refl a, a, IsConj.refl a, ha⟩
  simpa using mem_pow_add hg h1

end Vaserstein
