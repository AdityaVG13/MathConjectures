import Vaserstein.Exception

/-!
# Case C: `α` has a J1 block

Let `dim V = n ≥ 5`, `α ≠ 1` with a J1 block, `α = 1 ⊕ α'`, and assume the result in
dimensions `n - 1` and `n - 2` (`Covers`).

* A target `h ≠ 1` with a J1 block is `1 ⊕ h'`; induction in dimension `n - 1` puts `h'` in
  `C_{α'}^k` for every `k ≥ n - 1`, so `h ∈ C^k` (`caseC_J1`).
* Any other target `g ≠ 1`: Lemma P gives `c ∈ C` with `g c⁻¹` having a J1 block, and
  `g c⁻¹ ≠ 1` because `g` has no J1 block while `c` does. So `g ∈ C^(n-1) C = C^n`. The
  exception of Lemma P is `exception`.

`exists_conj_ne` shows that `α ≠ 1` is not central, which lets `covers_of_le` pass from `n`
factors to any `k ≥ n`.
-/

namespace Vaserstein

open Module Pointwise

universe u

section

variable {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

local notation "End" => V →ₗ[ZMod 2] V

theorem caseC_J1 {n : ℕ} (hV : finrank (ZMod 2) V = n) (hcov : Covers.{u} (n - 1))
    {α h : GLV (ZMod 2) V} (hα : α ≠ 1) (hJα : HasJ1 α) (hh : h ≠ 1) (hJh : HasJ1 h) {k : ℕ}
    (hk : n - 1 ≤ k) : h ∈ conjugatesOf α ^ k := by
  obtain ⟨Ka, Ea, α', hda, rfl⟩ := hJα.exists_blk
  obtain ⟨Kh, Eh, h', hdh, rfl⟩ := hJh.exists_blk
  have hα' : α' ≠ 1 := by
    rintro rfl
    exact hα (map_one (blk Ea))
  have hh' : h' ≠ 1 := by
    rintro rfl
    exact hh (map_one (blk Eh))
  let s : Ka ≃ₗ[ZMod 2] Kh := LinearEquiv.ofFinrankEq _ _ (by omega)
  have h1 := hcov Kh (by omega) (conjGL s α') h' (conjGL_ne_one hα') hh' k (by omega)
  have h2 := map_mem_conjugatesOf_pow ((blk Eh).comp (MonoidHom.inr _ _)) h1
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inr_apply] at h2
  rwa [isConj_iff_conjugatesOf_eq.1 (isConj_blk Ea Eh s 1 α')]

theorem caseC {n : ℕ} (hV : finrank (ZMod 2) V = n) (hn : 5 ≤ n) (hcov1 : Covers.{u} (n - 1))
    (hcov2 : Covers.{u} (n - 2)) {α g : GLV (ZMod 2) V} (hα : α ≠ 1) (hJ : HasJ1 α)
    (hg : g ≠ 1) : g ∈ conjugatesOf α ^ n := by
  by_cases hgJ : HasJ1 g
  · exact caseC_J1 hV hcov1 hα hJ hg hgJ (by omega)
  by_cases hω : α * α = 1 ∧ OmegaType g
  · exact exception hV hn hcov2 hα hω.1 hω.2
  obtain ⟨c, hc, hJh⟩ := lemmaP hα hJ hg (fun h1 h2 => hω ⟨h1, h2⟩)
  have hh : g * c⁻¹ ≠ 1 := by
    intro h
    rw [mul_inv_eq_one] at h
    exact hgJ (h ▸ hJ.of_isConj hc)
  have h1 := mul_mem_pow_succ (caseC_J1 hV hcov1 hα hJ hh hJh le_rfl) hc
  rw [show n - 1 + 1 = n by omega] at h1
  simpa using h1

/-- An upper unitriangular element of `GL₂(F₂)`. -/
def ρM : GL (Fin 2) (ZMod 2) := ⟨!![1, 1; 0, 1], !![1, 1; 0, 1], by decide, by decide⟩

theorem ρ2_apply (c : Fin 2 → ZMod 2) :
    ((Matrix.GeneralLinearGroup.toLin ρM : GLV (ZMod 2) (Fin 2 → ZMod 2)) :
      (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2)) c = ![c 0 + c 1, c 1] := by
  funext i
  fin_cases i <;> simp [ρM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

omit [FiniteDimensional (ZMod 2) V] in
/-- A nonidentity element of `GL(V)` over `F₂` is not central. -/
theorem exists_conj_ne {α : GLV (ZMod 2) V} (hα : α ≠ 1) : ∃ x, x * α * x⁻¹ ≠ α := by
  obtain ⟨v, hv⟩ := GLV.ne_one_iff.1 hα
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have hαv0 : (α : End) v ≠ 0 := by
    intro h
    apply hv0
    have := congrArg (↑α⁻¹ : End) h
    simpa using this
  obtain ⟨φ0, h01, h00⟩ := exists_dual_one (notMem_span_singleton_F2 hv0 hv.symm)
  obtain ⟨φ1, h11, h10⟩ := exists_dual_one (notMem_span_singleton_F2 hαv0 hv)
  have hb : Biorth ![v, (α : End) v] ![φ0, φ1] := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [h01, h11, h00 _ (Submodule.mem_span_singleton_self _),
        h10 _ (Submodule.mem_span_singleton_self _)]
  have e0 : frameEquiv hb v = (fun i => if i = 0 then 1 else 0, 0) := frameEquiv_e hb 0
  have e1 : frameEquiv hb ((α : End) v) = (fun i => if i = 1 then 1 else 0, 0) :=
    frameEquiv_e hb 1
  refine ⟨blk (frameEquiv hb) (Matrix.GeneralLinearGroup.toLin ρM, 1), fun h => hv0 ?_⟩
  rw [mul_inv_eq_iff_eq_mul] at h
  have := congrArg (fun u : GLV (ZMod 2) V => (u : End) v) h
  simp only [GLV.mul_apply, blk_apply, e0, e1, ρ2_apply, map_zero] at this
  simpa [Fin.sum_univ_two] using this

/-- Case C with any number `k ≥ n` of factors. -/
theorem caseC_ge {n : ℕ} (hV : finrank (ZMod 2) V = n) (hn : 5 ≤ n) (hcov1 : Covers.{u} (n - 1))
    (hcov2 : Covers.{u} (n - 2)) {α : GLV (ZMod 2) V} (hα : α ≠ 1) (hJ : HasJ1 α)
    (g : GLV (ZMod 2) V) (hg : g ≠ 1) (k : ℕ) (hk : n ≤ k) : g ∈ conjugatesOf α ^ k :=
  covers_of_le (exists_conj_ne hα) hk (fun _ hg => caseC hV hn hcov1 hcov2 hα hJ hg) g hg

end

end Vaserstein
