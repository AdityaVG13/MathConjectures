import Vaserstein.LemmaP

/-!
# The exception of Lemma P

Lemma P needs `g² + g + 1 ≠ 0` when `α` is an involution. This file treats the remaining case:
`α` an involution with a J1 block and `g² + g + 1 = 0` (`OmegaType g`).

Both maps split off a plane: `g = ω ⊕ g'` and `α = σ ⊕ α'`, where `σ` and `ω` are the
elements of `GL₂(F₂)` of orders `2` and `3` (`omega_frame`, `involution_frame`). In `GL₂(F₂)`,
`ω` is a product of two conjugates of `σ`, and so of any even number of them. The dimension
is even (`even_finrank_of_omega`).

* If `α' ≠ 1`, then `g' ∈ C_{α'}^n` by induction, and `g = ω ⊕ g'` is in `C^n`.
* If `α' = 1` (`α` is a transvection), write `g = (ω ⊕ 1)(1 ⊕ g')`. The first factor is a
  product of two transvections and the second of `n - 2`, by induction applied to a
  transvection of the smaller space.
-/

namespace Vaserstein

open Module Pointwise

universe u

/-- Every nonidentity element of `GL(W)`, `dim W = m`, is a product of `k` conjugates of any
nonidentity element, for every `k ≥ m`. -/
def Covers (m : ℕ) : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W],
    finrank (ZMod 2) W = m → ∀ a b : GLV (ZMod 2) W, a ≠ 1 → b ≠ 1 →
      ∀ k, m ≤ k → b ∈ conjugatesOf a ^ k

section GL2

/-- The swap of the two coordinates of `F₂²`. -/
def σM : GL (Fin 2) (ZMod 2) := ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by decide, by decide⟩

/-- An element of order `3` of `GL₂(F₂)`. -/
def ωM : GL (Fin 2) (ZMod 2) := ⟨!![0, 1; 1, 1], !![1, 1; 1, 0], by decide, by decide⟩

theorem ωM_mem : ωM ∈ conjugatesOf σM ^ 2 := by
  rw [pow_two]
  exact ⟨σM, IsConj.refl _, ωM * σM * ωM⁻¹, isConj_iff.2 ⟨ωM, rfl⟩, by decide⟩

theorem σM_mul_self : σM * σM = 1 := by decide

/-- `σ` acting on `F₂²`. -/
def σ2 : GLV (ZMod 2) (Fin 2 → ZMod 2) := Matrix.GeneralLinearGroup.toLin σM

/-- `ω` acting on `F₂²`. -/
def ω2 : GLV (ZMod 2) (Fin 2 → ZMod 2) := Matrix.GeneralLinearGroup.toLin ωM

theorem σ2_apply (c : Fin 2 → ZMod 2) :
    ((σ2 : GLV (ZMod 2) (Fin 2 → ZMod 2)) : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2)) c =
      ![c 1, c 0] := by
  funext i
  fin_cases i <;> simp [σ2, σM, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]

theorem ω2_apply (c : Fin 2 → ZMod 2) :
    ((ω2 : GLV (ZMod 2) (Fin 2 → ZMod 2)) : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2)) c =
      ![c 1, c 0 + c 1] := by
  funext i
  fin_cases i <;> simp [ω2, ωM, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]

theorem σ2_ne_one : σ2 ≠ 1 := by
  intro h
  have := congrArg (fun u : GLV (ZMod 2) (Fin 2 → ZMod 2) =>
    (u : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2)) ![1, 0] 0) h
  simp [σ2_apply] at this

theorem σ2_mul_self : σ2 * σ2 = 1 := by
  rw [σ2, ← map_mul, σM_mul_self, map_one]

theorem ω2_mem_two_mul (j : ℕ) : ω2 ∈ conjugatesOf σ2 ^ (2 + 2 * j) := by
  induction j with
  | zero => exact map_mem_conjugatesOf_pow Matrix.GeneralLinearGroup.toLin.toMonoidHom ωM_mem
  | succ j ih =>
    rw [show 2 + 2 * (j + 1) = 2 + 2 * j + 2 by ring]
    exact mem_pow_add_two σ2_mul_self ih

theorem ω2_mem_of_even {n : ℕ} (hn : Even n) (h2 : 2 ≤ n) : ω2 ∈ conjugatesOf σ2 ^ n := by
  obtain ⟨r, rfl⟩ := hn
  obtain ⟨j, hj⟩ : ∃ j, r + r = 2 + 2 * j := ⟨r - 1, by omega⟩
  rw [hj]
  exact ω2_mem_two_mul j

end GL2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

local notation "End" => V →ₗ[ZMod 2] V

/-- `g² + g + 1 = 0`. -/
def OmegaType (g : GLV (ZMod 2) V) : Prop := (g : End) * (g : End) + (g : End) + 1 = 0

theorem OmegaType.apply_apply {g : GLV (ZMod 2) V} (hg : OmegaType g) (x : V) :
    (g : End) ((g : End) x) = (g : End) x + x := by
  have := congrArg (fun f : End => f x) hg
  simp only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply,
    LinearMap.zero_apply, add_assoc] at this
  exact eq_of_add_eq_zero_F2 this

theorem OmegaType.inv_apply {g : GLV (ZMod 2) V} (hg : OmegaType g) (x : V) :
    (↑g⁻¹ : End) x = (g : End) x + x := by
  have h : (g : End) ((g : End) x + x) = x := by
    rw [map_add, hg.apply_apply]
    abel_nf
    simp
  calc (↑g⁻¹ : End) x = (↑g⁻¹ : End) ((g : End) ((g : End) x + x)) := by rw [h]
    _ = (g : End) x + x := GLV.inv_apply_apply _ _

theorem OmegaType.apply_ne_self {g : GLV (ZMod 2) V} (hg : OmegaType g) {x : V} (hx : x ≠ 0) :
    (g : End) x ≠ x := by
  intro h
  have := hg.apply_apply x
  rw [h, h, add_self_eq_zero_F2] at this
  exact hx this

/-- `g = ω ⊕ g'` along a frame through any nonzero vector. -/
theorem omega_frame [FiniteDimensional (ZMod 2) V] {g : GLV (ZMod 2) V} (hg : OmegaType g)
    {v : V} (hv : v ≠ 0) :
    ∃ (K : Submodule (ZMod 2) V) (E : V ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) × K) (g' : GLV (ZMod 2) K),
      finrank (ZMod 2) V = 2 + finrank (ZMod 2) K ∧ blk E (ω2, g') = g ∧ OmegaType g' := by
  obtain ⟨φ, hφ1, hφ0⟩ :=
    exists_dual_one (notMem_span_singleton_F2 hv (hg.apply_ne_self hv).symm)
  have hφg : φ ((g : End) v) = 0 := hφ0 _ (Submodule.mem_span_singleton_self _)
  have hb : Biorth ![v, (g : End) v] ![φ, φ ∘ₗ (g : End)] := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hφ1, hφg, hg.apply_apply]
  have hK : ∀ x ∈ frameKer ![φ, φ ∘ₗ (g : End)], (g : End) x ∈ frameKer ![φ, φ ∘ₗ (g : End)] := by
    intro x hx
    rw [mem_frameKer] at hx ⊢
    have h0 := hx 0
    have h1 := hx 1
    simp at h0 h1
    intro i
    fin_cases i <;> simp [h0, h1, hg.apply_apply]
  have hK' : ∀ x ∈ frameKer ![φ, φ ∘ₗ (g : End)],
      (↑g⁻¹ : End) x ∈ frameKer ![φ, φ ∘ₗ (g : End)] := by
    intro x hx
    rw [hg.inv_apply]
    exact Submodule.add_mem _ (hK x hx) hx
  refine ⟨_, frameEquiv hb, restrictGL g _ hK hK', finrank_frameKer hb, ?_, ?_⟩
  · apply blk_frameEquiv
    intro c
    simp only [Fin.sum_univ_two, ω2_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      hg.apply_apply, add_smul, smul_add]
    abel
  · ext x
    simp [hg.apply_apply, add_assoc, add_self_eq_zero_F2]

/-- An involution is `σ ⊕ α'` along a frame through any vector it moves. -/
theorem involution_frame [FiniteDimensional (ZMod 2) V] {α : GLV (ZMod 2) V} (hα : α * α = 1)
    {u : V} (hu : (α : End) u ≠ u) :
    ∃ (K : Submodule (ZMod 2) V) (E : V ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) × K) (α' : GLV (ZMod 2) K),
      finrank (ZMod 2) V = 2 + finrank (ZMod 2) K ∧ blk E (σ2, α') = α ∧ α' * α' = 1 := by
  have hαα : ∀ x, (α : End) ((α : End) x) = x := fun x => by
    rw [← GLV.mul_apply, hα, GLV.one_apply]
  have hinv : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  obtain ⟨ψ, hψ1, hψ0⟩ := exists_dual_one (notMem_span_singleton_F2 hu0 hu.symm)
  have hψα : ψ ((α : End) u) = 0 := hψ0 _ (Submodule.mem_span_singleton_self _)
  have hb : Biorth ![u, (α : End) u] ![ψ, ψ ∘ₗ (α : End)] := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hψ1, hψα, hαα]
  have hK : ∀ x ∈ frameKer ![ψ, ψ ∘ₗ (α : End)], (α : End) x ∈ frameKer ![ψ, ψ ∘ₗ (α : End)] := by
    intro x hx
    rw [mem_frameKer] at hx ⊢
    have h0 := hx 0
    have h1 := hx 1
    simp at h0 h1
    intro i
    fin_cases i <;> simp [h0, h1, hαα]
  have hK' : ∀ x ∈ frameKer ![ψ, ψ ∘ₗ (α : End)],
      (↑α⁻¹ : End) x ∈ frameKer ![ψ, ψ ∘ₗ (α : End)] := by
    rw [hinv]
    exact hK
  refine ⟨_, frameEquiv hb, restrictGL α _ hK hK', finrank_frameKer hb, ?_, ?_⟩
  · apply blk_frameEquiv
    intro c
    simp only [Fin.sum_univ_two, σ2_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hαα]
    abel
  · apply GLV.ext
    intro x
    ext
    simp [hαα]

theorem OmegaType.ne_one [Nontrivial V] {g : GLV (ZMod 2) V} (hg : OmegaType g) : g ≠ 1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  intro h
  exact hg.apply_ne_self hx (by simp [h])

theorem even_finrank_of_omega : ∀ (m : ℕ) {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W], finrank (ZMod 2) W = m →
      ∀ g : GLV (ZMod 2) W, OmegaType g → Even m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro W _ _ _ hW g hg
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨0, rfl⟩
    · obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2) (M := W)).1
        (hW ▸ hm)
      obtain ⟨K, E, g', hdim, -, hg'⟩ := omega_frame hg hv
      have := ih (finrank (ZMod 2) K) (by omega) rfl g' hg'
      rw [← hW, hdim]
      exact even_two.add this

/-- **The exception.** `α` an involution with a J1 block, `g² + g + 1 = 0`. -/
theorem exception {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {n : ℕ} (hV : finrank (ZMod 2) V = n) (hn : 5 ≤ n) (hcov : Covers.{u} (n - 2))
    {α g : GLV (ZMod 2) V} (hα : α ≠ 1) (hinv : α * α = 1) (hg : OmegaType g) :
    g ∈ conjugatesOf α ^ n := by
  have heven : Even n := even_finrank_of_omega n hV g hg
  obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2) (M := V)).1 (by omega)
  obtain ⟨Kg, Eg, g', hdg, rfl, hg'⟩ := omega_frame hg hv
  obtain ⟨u, hu⟩ := GLV.ne_one_iff.1 hα
  obtain ⟨Ka, Ea, α', hda, rfl, -⟩ := involution_frame hinv hu
  have hdKg : finrank (ZMod 2) Kg = n - 2 := by omega
  have hKg : Nontrivial Kg := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hg'1 : g' ≠ 1 := hg'.ne_one
  let s : Ka ≃ₗ[ZMod 2] Kg := LinearEquiv.ofFinrankEq _ _ (by omega)
  by_cases hα' : α' = 1
  · subst hα'
    have hconj := isConj_blk Ea Eg s σ2 1
    rw [map_one] at hconj
    -- `ω ⊕ 1` is a product of two conjugates of `α`
    have h1 : blk Eg (ω2, 1) ∈ conjugatesOf (blk Ea (σ2, 1)) ^ 2 := by
      rw [isConj_iff_conjugatesOf_eq.1 hconj]
      apply map_mem_conjugatesOf_pow (blk Eg)
      apply prod_mem_conjugatesOf_pow (ω2_mem_two_mul 0)
      rw [pow_two]
      exact ⟨1, IsConj.refl _, 1, IsConj.refl _, mul_one 1⟩
    -- `1 ⊕ g'` is a product of `n - 2` conjugates of `α`
    obtain ⟨v', hv'⟩ := exists_ne (0 : Kg)
    obtain ⟨K'', E'', -, hd'', -, -⟩ := omega_frame hg' hv'
    have hτ : blk E'' (σ2, 1) ≠ 1 := fun h => σ2_ne_one (congrArg Prod.fst (blk_eq_one h))
    have h2' := hcov Kg hdKg (blk E'' (σ2, 1)) g' hτ hg'1 (n - 2) le_rfl
    have h2 := map_mem_conjugatesOf_pow ((blk Eg).comp (MonoidHom.inr _ _)) h2'
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inr_apply] at h2
    rw [blk_one_blk] at h2
    let s' : Ka ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) × K'' := LinearEquiv.ofFinrankEq _ _ (by
      rw [Module.finrank_prod, Module.finrank_fin_fun]
      omega)
    have hconj' := isConj_blk Ea
      (Eg.trans (((LinearEquiv.refl (ZMod 2) _).prodCongr E'').trans (swap12 _ _))) s' σ2 1
    rw [map_one] at hconj'
    rw [← isConj_iff_conjugatesOf_eq.1 hconj'] at h2
    have := mem_pow_add h1 h2
    rw [show 2 + (n - 2) = n by omega, ← map_mul] at this
    simpa using this
  · have h2 := hcov Kg hdKg (conjGL s α') g' (conjGL_ne_one hα') hg'1 n (by omega)
    have h12 := prod_mem_conjugatesOf_pow (ω2_mem_of_even heven (by omega)) h2
    rw [isConj_iff_conjugatesOf_eq.1 (isConj_blk Ea Eg s σ2 α')]
    exact map_mem_conjugatesOf_pow (blk Eg) h12

end Vaserstein
