import Mathlib.FieldTheory.Finite.Basic
import Vaserstein.Linear

/-!
# J1 blocks and Lemma P over `F₂`

An invertible map `h` *has a J1 block* if it fixes a vector `v` and a covector `φ` with
`φ v = 1`; then `h = 1 ⊕ h'` on `⟨v⟩ ⊕ ker φ` (`HasJ1.exists_blk`).

Lemma P (`lemmaP`). Let `α ≠ 1` have a J1 block and let `g ≠ 1`. If `α` is an involution,
assume also `g² + g + 1 ≠ 0`. Then some conjugate `c` of `α` makes `g c⁻¹` have a J1 block.

The proof picks `v` and `φ` with `φ v = 1`, `φ (g v) = 0` (and `φ (g⁻¹ v) = 0` for an
involution), and a matching pair `w'`, `φ'` on the side of `α`. The two quadruples are
completed to frames with the same pairing, and `c` is `α` transported from one frame to the
other.
-/

namespace Vaserstein

open Module

section F2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

theorem add_self_eq_zero_F2 (x : V) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

@[simp] theorem two_zsmul_F2 (x : V) : (2 : ℤ) • x = 0 := by
  rw [two_zsmul]
  exact add_self_eq_zero_F2 x

@[simp] theorem three_zsmul_F2 (x : V) : (3 : ℤ) • x = x := by
  rw [show (3 : ℤ) = 2 + 1 from rfl, add_zsmul, two_zsmul_F2, zero_add, one_zsmul]

theorem eq_of_add_eq_zero_F2 {x y : V} (h : x + y = 0) : x = y := by
  calc x = x + (y + y) := by rw [add_self_eq_zero_F2, add_zero]
    _ = y := by rw [← add_assoc, h, zero_add]

theorem notMem_span_singleton_F2 {x y : V} (h0 : x ≠ 0) (h1 : x ≠ y) :
    x ∉ Submodule.span (ZMod 2) {y} := by
  rw [Submodule.mem_span_singleton]
  rintro ⟨a, hab⟩
  rcases zmod2_cases a with rfl | rfl
  · exact h0 (by simpa using hab.symm)
  · exact h1 (by simpa using hab.symm)

theorem notMem_span_pair_F2 {x y z : V} (h0 : x ≠ 0) (h1 : x ≠ y) (h2 : x ≠ z)
    (h3 : x ≠ y + z) : x ∉ Submodule.span (ZMod 2) {y, z} := by
  rw [Submodule.mem_span_pair]
  rintro ⟨a, b, hab⟩
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · exact h0 (by simpa using hab.symm)
  · exact h2 (by simpa using hab.symm)
  · exact h1 (by simpa using hab.symm)
  · exact h3 (by simpa using hab.symm)

/-- A space is not the union of two proper subspaces. -/
theorem exists_notMem_notMem {p q : Submodule (ZMod 2) V} (hp : p ≠ ⊤) (hq : q ≠ ⊤) :
    ∃ x, x ∉ p ∧ x ∉ q := by
  obtain ⟨a, -, ha⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hp)
  obtain ⟨b, -, hb⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hq)
  by_cases haq : a ∈ q
  · by_cases hbp : b ∈ p
    · refine ⟨a + b, fun h => ha ?_, fun h => hb ?_⟩
      · simpa using p.sub_mem h hbp
      · simpa using q.sub_mem h haq
    · exact ⟨b, hbp, hb⟩
  · exact ⟨a, ha, haq⟩

end F2

theorem exists_dual_one {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {p : Submodule F V} {x : V} (hx : x ∉ p) : ∃ φ : Dual F V, φ x = 1 ∧ ∀ y ∈ p, φ y = 0 := by
  obtain ⟨f, hfx, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  refine ⟨(f x)⁻¹ • f, by simp [hfx], fun y hy => ?_⟩
  have : f y ∈ p.map f := Submodule.mem_map_of_mem hy
  rw [hf, Submodule.mem_bot] at this
  simp [this]

section J1

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

local notation "End" => V →ₗ[ZMod 2] V

/-- `h` fixes a vector `v` and a covector `φ` with `φ v = 1`. -/
def HasJ1 (h : GLV (ZMod 2) V) : Prop :=
  ∃ (v : V) (φ : Dual (ZMod 2) V), φ v = 1 ∧ (h : End) v = v ∧ ∀ x, φ ((h : End) x) = φ x

theorem HasJ1.conj {h : GLV (ZMod 2) V} (hJ : HasJ1 h) (x : GLV (ZMod 2) V) :
    HasJ1 (x * h * x⁻¹) := by
  obtain ⟨v, φ, h1, h2, h3⟩ := hJ
  exact ⟨(x : End) v, φ ∘ₗ (↑x⁻¹ : End), by simp [h1], by simp [h2], fun y => by simp [h3]⟩

theorem HasJ1.of_isConj {a b : GLV (ZMod 2) V} (hab : IsConj a b) (hJ : HasJ1 a) : HasJ1 b := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hab
  exact hJ.conj c

/-- A map with a J1 block is `1 ⊕ h'` along a splitting `V ≃ F₂ × K`. -/
theorem HasJ1.exists_blk [FiniteDimensional (ZMod 2) V] {h : GLV (ZMod 2) V} (hJ : HasJ1 h) :
    ∃ (K : Submodule (ZMod 2) V) (E : V ≃ₗ[ZMod 2] (Fin 1 → ZMod 2) × K)
      (h' : GLV (ZMod 2) K), finrank (ZMod 2) V = 1 + finrank (ZMod 2) K ∧ blk E (1, h') = h := by
  obtain ⟨v, φ, h1, h2, h3⟩ := hJ
  have hb : Biorth ![v] ![φ] := by
    intro i j
    fin_cases i
    fin_cases j
    simp [h1]
  have hK : ∀ x ∈ frameKer ![φ], (h : End) x ∈ frameKer ![φ] := by
    intro x hx
    rw [mem_frameKer] at hx ⊢
    intro i
    fin_cases i
    simpa [h3] using hx 0
  have hK' : ∀ x ∈ frameKer ![φ], (↑h⁻¹ : End) x ∈ frameKer ![φ] := by
    intro x hx
    rw [mem_frameKer] at hx ⊢
    intro i
    fin_cases i
    have := h3 ((↑h⁻¹ : End) x)
    simp only [GLV.apply_inv_apply] at this
    simpa [← this] using hx 0
  refine ⟨_, frameEquiv hb, restrictGL h _ hK hK', finrank_frameKer hb, ?_⟩
  apply blk_frameEquiv
  intro c
  simp [h2]

end J1

section LemmaP

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

local notation "End" => V →ₗ[ZMod 2] V

/-- The frame step of Lemma P. -/
theorem lemmaP_core {α g : GLV (ZMod 2) V} {v w' : V} {φ φ' : Dual (ZMod 2) V}
    (h1 : φ v = 1) (h2 : φ ((g : End) v) = 0)
    (h3 : φ' w' = φ ((↑g⁻¹ : End) v)) (h4 : φ' ((α : End) w') = 1)
    (h5 : φ' ((α : End) ((α : End) w')) = 0) :
    ∃ c ∈ conjugatesOf α, HasJ1 (g * c⁻¹) := by
  have hb : Biorth ![(↑g⁻¹ : End) v, v]
      ![φ ∘ₗ (g : End), φ - φ ((↑g⁻¹ : End) v) • (φ ∘ₗ (g : End))] := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [h1, h2]
  have hb' : Biorth ![w', (α : End) w']
      ![φ' ∘ₗ (α : End), φ' - φ ((↑g⁻¹ : End) v) • (φ' ∘ₗ (α : End))] := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [h3, h4, h5]
  have hdim : finrank (ZMod 2) (frameKer ![φ' ∘ₗ (α : End),
        φ' - φ ((↑g⁻¹ : End) v) • (φ' ∘ₗ (α : End))]) =
      finrank (ZMod 2) (frameKer ![φ ∘ₗ (g : End),
        φ - φ ((↑g⁻¹ : End) v) • (φ ∘ₗ (g : End))]) := by
    have := finrank_frameKer hb
    have := finrank_frameKer hb'
    omega
  set t := frameTransport hb' hb (LinearEquiv.ofFinrankEq _ _ hdim)
  have te0 : t w' = (↑g⁻¹ : End) v := frameTransport_e hb' hb _ 0
  have te1 : t ((α : End) w') = v := frameTransport_e hb' hb _ 1
  have tf0 : ∀ y, φ ((g : End) (t y)) = φ' ((α : End) y) := frameTransport_f hb' hb _ 0
  have tf1 := frameTransport_f hb' hb (LinearEquiv.ofFinrankEq _ _ hdim) 1
  have tφ : ∀ y, φ (t y) = φ' y := by
    intro y
    have h := tf1 y
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.comp_apply] at h
    rw [tf0] at h
    exact sub_left_inj.1 h
  have hts : t.symm v = (α : End) w' := by
    rw [LinearEquiv.symm_apply_eq]
    exact te1.symm
  have hc : ∀ x, ((g * (GLV.ofEquiv t * α * (GLV.ofEquiv t)⁻¹)⁻¹ : GLV (ZMod 2) V) : End) x =
      (g : End) (t ((↑α⁻¹ : End) (t.symm x))) := by
    intro x
    simp [mul_assoc]
  refine ⟨GLV.ofEquiv t * α * (GLV.ofEquiv t)⁻¹, isConj_iff.2 ⟨_, rfl⟩, v, φ, h1, ?_, ?_⟩
  · rw [hc, hts, GLV.inv_apply_apply, te0, GLV.apply_inv_apply]
  · intro x
    rw [hc, tf0, GLV.apply_inv_apply, ← tφ, LinearEquiv.apply_symm_apply]

/-- **Lemma P.** -/
theorem lemmaP {α g : GLV (ZMod 2) V} (hα : α ≠ 1) (hJ : HasJ1 α) (hg : g ≠ 1)
    (hω : α * α = 1 → (g : End) * (g : End) + (g : End) + 1 ≠ 0) :
    ∃ c ∈ conjugatesOf α, HasJ1 (g * c⁻¹) := by
  have gg : ∀ x, (g : End) ((↑g⁻¹ : End) x) = x := GLV.apply_inv_apply g
  by_cases hinv : α * α = 1
  · have hq := hω hinv
    have hp' : LinearMap.ker ((g : End) - 1) ≠ ⊤ := by
      intro h
      apply hg
      apply GLV.ext
      intro x
      have : x ∈ LinearMap.ker ((g : End) - 1) := h ▸ Submodule.mem_top
      simpa [sub_eq_zero] using this
    have hq' : LinearMap.ker ((g : End) * (g : End) + (g : End) + 1) ≠ ⊤ := by
      intro h
      apply hq
      ext x
      have : x ∈ LinearMap.ker ((g : End) * (g : End) + (g : End) + 1) := h ▸ Submodule.mem_top
      simpa using this
    obtain ⟨v, hv1, hv2⟩ := exists_notMem_notMem hp' hq'
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
      LinearMap.add_apply, Module.End.mul_apply] at hv1 hv2
    have hv0 : v ≠ 0 := by rintro rfl; simp at hv1
    have hsp : v ∉ Submodule.span (ZMod 2) {(g : End) v, (↑g⁻¹ : End) v} := by
      refine notMem_span_pair_F2 hv0 (Ne.symm hv1) (fun h => hv1 ?_) (fun h => hv2 ?_)
      · conv_lhs => rw [h]
        exact gg v
      · have e : (g : End) v = (g : End) ((g : End) v) + v := by
          conv_lhs => rw [h]
          rw [map_add, gg]
        calc (g : End) ((g : End) v) + (g : End) v + v
            = (g : End) ((g : End) v) + ((g : End) ((g : End) v) + v) + v := by rw [← e]
          _ = 0 := by abel_nf; simp
    obtain ⟨φ, hφ1, hφ0⟩ := exists_dual_one hsp
    obtain ⟨w', hw'⟩ := GLV.ne_one_iff.1 hα
    have hw0 : (α : End) w' ≠ 0 := by
      intro h
      apply hw'
      rw [h]
      have := congrArg (↑α⁻¹ : End) h
      simpa using this.symm
    obtain ⟨φ', hφ'1, hφ'0⟩ := exists_dual_one (notMem_span_singleton_F2 hw0 hw')
    have hαα : (α : End) ((α : End) w') = w' := by
      rw [← GLV.mul_apply, hinv, GLV.one_apply]
    refine lemmaP_core hφ1 (hφ0 _ (Submodule.subset_span (by simp))) ?_ hφ'1 ?_
    · rw [hφ'0 _ (Submodule.mem_span_singleton_self _),
        hφ0 _ (Submodule.subset_span (by simp))]
    · rw [hαα]
      exact hφ'0 _ (Submodule.mem_span_singleton_self _)
  · obtain ⟨v, hv⟩ := GLV.ne_one_iff.1 hg
    have hv0 : v ≠ 0 := by rintro rfl; simp at hv
    obtain ⟨φ, hφ1, hφ0⟩ := exists_dual_one (notMem_span_singleton_F2 hv0 (Ne.symm hv))
    obtain ⟨u, ψ, hψ, hu, -⟩ := hJ
    have hp' : LinearMap.ker ((α : End) * (α : End) - 1) ≠ ⊤ := by
      intro h
      apply hinv
      apply GLV.ext
      intro x
      have : x ∈ LinearMap.ker ((α : End) * (α : End) - 1) := h ▸ Submodule.mem_top
      simpa [sub_eq_zero] using this
    have hq' : LinearMap.ker ((α : End) * (α : End) + (α : End) + 1) ≠ ⊤ := by
      intro h
      have : u ∈ LinearMap.ker ((α : End) * (α : End) + (α : End) + 1) := h ▸ Submodule.mem_top
      simp only [LinearMap.mem_ker, LinearMap.add_apply, Module.End.mul_apply,
        Module.End.one_apply, hu] at this
      have h0 : u = 0 := by
        rw [add_self_eq_zero_F2, zero_add] at this
        exact this
      simp [h0] at hψ
    obtain ⟨w', hw1, hw2⟩ := exists_notMem_notMem hp' hq'
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
      LinearMap.add_apply, Module.End.mul_apply] at hw1 hw2
    have hw0 : w' ≠ 0 := by rintro rfl; simp at hw1
    have hαw : (α : End) w' ≠ w' := by
      intro h
      apply hw1
      rw [h, h]
    have hαw0 : (α : End) w' ≠ 0 := by
      intro h
      apply hw0
      have := congrArg (↑α⁻¹ : End) h
      simpa using this
    have hs0 : w' ∉ Submodule.span (ZMod 2) {(α : End) w', (α : End) ((α : End) w')} := by
      refine notMem_span_pair_F2 hw0 (Ne.symm hαw) (Ne.symm hw1) (fun h => hw2 ?_)
      calc (α : End) ((α : End) w') + (α : End) w' + w'
          = (α : End) ((α : End) w') + (α : End) w' + ((α : End) w' + (α : End) ((α : End) w')) := by
            rw [← h]
        _ = 0 := by abel_nf; simp
    have hs1 : (α : End) w' ∉ Submodule.span (ZMod 2) {w', (α : End) ((α : End) w')} := by
      refine notMem_span_pair_F2 hαw0 hαw (fun h => hαw ?_) (fun h => hw2 ?_)
      · have := congrArg (↑α⁻¹ : End) h
        simpa using this.symm
      · calc (α : End) ((α : End) w') + (α : End) w' + w'
            = (α : End) ((α : End) w') + (w' + (α : End) ((α : End) w')) + w' := by rw [← h]
          _ = 0 := by abel_nf; simp
    obtain ⟨φ0, hφ01, hφ00⟩ := exists_dual_one hs0
    obtain ⟨φ1, hφ11, hφ10⟩ := exists_dual_one hs1
    refine lemmaP_core (w' := w') (φ' := φ ((↑g⁻¹ : End) v) • φ0 + φ1) hφ1
      (hφ0 _ (Submodule.mem_span_singleton_self _)) ?_ ?_ ?_
    · simp [hφ01, hφ10 _ (Submodule.subset_span (by simp : w' ∈ _))]
    · simp [hφ11, hφ00 _ (Submodule.subset_span (by simp : (α : End) w' ∈ _))]
    · simp [hφ00 _ (Submodule.subset_span (by simp : (α : End) ((α : End) w') ∈ _)),
        hφ10 _ (Submodule.subset_span (by simp : (α : End) ((α : End) w') ∈ _))]

end LemmaP

end Vaserstein
