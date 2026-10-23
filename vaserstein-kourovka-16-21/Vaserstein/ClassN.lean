import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.PrincipalIdealDomain
import Vaserstein.LemmaP

/-!
# The similarity class `N`

Let `dim V = n ≥ 3` over `F₂` and let `r` be monic irreducible of degree `n - 1`. Every
`u ∈ GL(V)` whose minimal polynomial is divisible by `r` has minimal polynomial `r (X + 1)`
(`minpoly_eq_of_dvd`) and a cyclic vector (`exists_cyclic`), and any two such elements are
conjugate (`isConj_of_dvd_minpoly`).
-/

namespace Vaserstein

open Module Polynomial

section Cyclic

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- If `m(f) = 0` for a monic `m` of degree `n`, then `f^n v = -∑_{j<n} m_j f^j v`. -/
theorem pow_apply_eq_of_aeval {f : V →ₗ[K] V} {m : K[X]} (hm : m.Monic) {n : ℕ}
    (hdeg : m.natDegree = n) (hf : aeval f m = 0) (v : V) :
    (f ^ n) v = -∑ j : Fin n, m.coeff j • (f ^ (j : ℕ)) v := by
  have h := congrArg (fun g : V →ₗ[K] V => g v) hf
  rw [hm.as_sum, hdeg] at h
  rw [eq_neg_iff_add_eq_zero]
  simpa [map_sum, Finset.sum_range, Algebra.smul_def] using h

variable [FiniteDimensional K V] in
/-- Two maps killed by the same monic polynomial of degree `dim V`, each with a cyclic vector,
are conjugate. -/
theorem exists_conj_of_cyclic {f f' : V →ₗ[K] V} {m : K[X]} (hm : m.Monic) {n : ℕ}
    (hdeg : m.natDegree = n) (hV : finrank K V = n) (hf : aeval f m = 0)
    (hf' : aeval f' m = 0) {v v' : V}
    (hv : LinearIndependent K (fun i : Fin n => (f ^ (i : ℕ)) v))
    (hv' : LinearIndependent K (fun i : Fin n => (f' ^ (i : ℕ)) v')) :
    ∃ φ : V ≃ₗ[K] V, ∀ x, φ (f x) = f' (φ x) := by
  have hc : Fintype.card (Fin n) = finrank K V := by simp [hV]
  let b := basisOfLinearIndependentOfCardEqFinrank' _ hv hc
  let b' := basisOfLinearIndependentOfCardEqFinrank' _ hv' hc
  have hb : ∀ i, b i = (f ^ (i : ℕ)) v := fun i => by simp [b]
  have hb' : ∀ i, b' i = (f' ^ (i : ℕ)) v' := fun i => by simp [b']
  set φ := b.equiv b' (Equiv.refl _)
  have hφ : ∀ i, φ (b i) = b' i := fun i => b.equiv_apply i b' (Equiv.refl _)
  refine ⟨φ, fun x => ?_⟩
  have key : φ.toLinearMap ∘ₗ f = f' ∘ₗ φ.toLinearMap := by
    refine b.ext fun i => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hφ]
    by_cases hi : (i : ℕ) + 1 < n
    · have e1 : f (b i) = b ⟨i + 1, hi⟩ := by
        rw [hb, hb, ← Module.End.mul_apply, ← pow_succ']
      have e2 : f' (b' i) = b' ⟨i + 1, hi⟩ := by
        rw [hb', hb', ← Module.End.mul_apply, ← pow_succ']
      rw [e1, e2, hφ]
    · have hi' : (i : ℕ) + 1 = n := by omega
      have e1 : f (b i) = -∑ j : Fin n, m.coeff j • b j := by
        rw [hb, ← Module.End.mul_apply, ← pow_succ', hi', pow_apply_eq_of_aeval hm hdeg hf]
        simp [hb]
      have e2 : f' (b' i) = -∑ j : Fin n, m.coeff j • b' j := by
        rw [hb', ← Module.End.mul_apply, ← pow_succ', hi', pow_apply_eq_of_aeval hm hdeg hf']
        simp [hb']
      rw [e1, e2]
      simp [map_neg, map_sum, map_smul, hφ]
  exact LinearMap.congr_fun key x

end Cyclic

section ClassN

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

local notation "End" => V →ₗ[ZMod 2] V

variable {n : ℕ} {r : (ZMod 2)[X]}

theorem minpoly_eq_of_dvd (hV : finrank (ZMod 2) V = n) (hn : 3 ≤ n) (hrm : r.Monic)
    (hri : Irreducible r) (hrd : r.natDegree = n - 1) {u : GLV (ZMod 2) V}
    (hr : r ∣ minpoly (ZMod 2) (u : End)) : minpoly (ZMod 2) (u : End) = r * (X + 1) := by
  set f := (u : End)
  have hint : IsIntegral (ZMod 2) f := Algebra.IsIntegral.isIntegral f
  have hmm := minpoly.monic hint
  obtain ⟨s, hs⟩ := hr.trans (LinearMap.minpoly_dvd_charpoly f)
  have hcm := LinearMap.charpoly_monic f
  have hsm : s.Monic := hrm.of_mul_monic_left (hs ▸ hcm)
  have hcd : f.charpoly.natDegree = n := (LinearMap.charpoly_natDegree f).trans hV
  have hsd : s.natDegree = 1 := by
    rw [hs, hrm.natDegree_mul hsm] at hcd
    omega
  have hdet : LinearMap.det f ≠ 0 := (u.isUnit.map LinearMap.det).ne_zero
  rw [LinearMap.det_eq_sign_charpoly_coeff, hs, mul_coeff_zero] at hdet
  have hs0 : s.coeff 0 = 1 := (zmod2_cases _).resolve_left fun h => hdet (by simp [h])
  have hc : f.charpoly = r * (X + 1) := by
    rw [hs, hsm.eq_X_add_C hsd, hs0, C_1]
  obtain ⟨t, ht⟩ := hr
  have hdvd : r * t ∣ r * (X + 1) := ht ▸ hc ▸ LinearMap.minpoly_dvd_charpoly f
  have htd : t ∣ X + 1 := (mul_dvd_mul_iff_left hrm.ne_zero).1 hdvd
  have htm : t.Monic := hrm.of_mul_monic_left (ht ▸ hmm)
  have hX1 : Irreducible (X + 1 : (ZMod 2)[X]) := by
    simpa using irreducible_of_degree_eq_one (degree_X_add_C (1 : ZMod 2))
  rcases hX1.dvd_iff.1 htd with h1 | h1
  · rw [htm.isUnit_iff] at h1
    have hroot : f.charpoly.IsRoot 1 := by
      rw [hc]
      simp only [IsRoot, eval_mul, eval_add, eval_X, eval_one]
      exact mul_eq_zero_of_right _ (by decide)
    have hmr := Module.End.hasEigenvalue_iff_isRoot.1
      ((Module.End.hasEigenvalue_iff_isRoot_charpoly f 1).2 hroot)
    rw [ht, h1, mul_one] at hmr
    have := degree_eq_one_of_irreducible_of_root hri hmr
    rw [degree_eq_natDegree hri.ne_zero, hrd] at this
    norm_cast at this
    omega
  · rw [ht, ← eq_of_monic_of_associated (monic_X_add_C 1) htm h1, C_1]

theorem natDegree_r_mul (hn : 3 ≤ n) (hrm : r.Monic) (hrd : r.natDegree = n - 1) :
    (r * (X + 1)).natDegree = n := by
  rw [natDegree_mul hrm.ne_zero (by simpa using X_add_C_ne_zero (1 : ZMod 2)), ← C_1,
    natDegree_X_add_C]
  omega

/-- A map `u` as in `minpoly_eq_of_dvd` has a cyclic vector: any `v` with `r(u) v ≠ 0` and
`(u + 1) v ≠ 0`. If `p(u) v = 0` with `p ≠ 0` of degree `< n`, either `r ∣ p`, so `p = c r`, or
`r` and `p` are coprime, which kills `(u + 1) v`. -/
theorem exists_cyclic (hV : finrank (ZMod 2) V = n) (hn : 3 ≤ n) (hrm : r.Monic)
    (hri : Irreducible r) (hrd : r.natDegree = n - 1) {u : GLV (ZMod 2) V}
    (hr : r ∣ minpoly (ZMod 2) (u : End)) :
    ∃ v : V, LinearIndependent (ZMod 2) (fun i : Fin n => ((u : End) ^ (i : ℕ)) v) := by
  set f := (u : End)
  have hmin := minpoly_eq_of_dvd hV hn hrm hri hrd hr
  have hmd := natDegree_r_mul hn hrm hrd
  have hm0 : aeval f (r * (X + 1)) = 0 := by rw [← hmin]; exact minpoly.aeval _ _
  have hA : aeval f r ≠ 0 := fun h => by
    have := natDegree_le_of_dvd (hmin ▸ minpoly.dvd (ZMod 2) f h) hrm.ne_zero
    omega
  have hB : aeval f (X + 1) ≠ 0 := fun h => by
    have := natDegree_le_of_dvd (hmin ▸ minpoly.dvd (ZMod 2) f h) (X_add_C_ne_zero 1)
    rw [natDegree_X_add_C] at this
    omega
  obtain ⟨v, hvA, hvB⟩ := exists_notMem_notMem (fun h => hA (LinearMap.ker_eq_top.1 h))
    (fun h => hB (LinearMap.ker_eq_top.1 h))
  rw [LinearMap.mem_ker] at hvA hvB
  refine ⟨v, Fintype.linearIndependent_iff.2 fun g hg i => ?_⟩
  set p := ∑ i : Fin n, C (g i) * X ^ (i : ℕ)
  have hpv : aeval f p v = 0 := by
    rw [← hg]
    simp [p, map_sum]
  have hp0 : p = 0 := by
    by_contra hp
    have hpd : p.natDegree < n := (natDegree_lt_iff_degree_lt hp).2 (degree_sum_fin_lt g)
    by_cases hrp : r ∣ p
    · obtain ⟨c, hc⟩ := hrp
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hp (by simpa using hc)
      have hcd : c.natDegree = 0 := by
        rw [hc, natDegree_mul hrm.ne_zero hc0] at hpd
        omega
      have hc00 : c.coeff 0 ≠ 0 := by
        intro h
        apply hc0
        rw [eq_C_of_natDegree_eq_zero hcd, h, C_0]
      rw [hc, eq_C_of_natDegree_eq_zero hcd] at hpv
      have : c.coeff 0 • aeval f r v = 0 := by
        rw [← hpv]
        simp
      exact hvA ((smul_eq_zero.1 this).resolve_left hc00)
    · obtain ⟨a, b, hab⟩ := hri.coprime_iff_not_dvd.2 hrp
      apply hvB
      have : aeval f (X + 1 : (ZMod 2)[X]) = aeval f a * aeval f (r * (X + 1)) +
          aeval f (b * (X + 1)) * aeval f p := by
        rw [← map_mul, ← map_mul, ← map_add]
        congr 1
        linear_combination -(X + 1 : (ZMod 2)[X]) * hab
      rw [this, hm0, mul_zero, zero_add, Module.End.mul_apply, hpv, map_zero]
  have := congrArg (fun q => coeff q i) hp0
  simpa [p, finsetSum_coeff, coeff_C_mul, coeff_X_pow, Fin.val_inj] using this

/-- Any two elements of `GL(V)` whose minimal polynomials are divisible by `r` are conjugate. -/
theorem isConj_of_dvd_minpoly (hV : finrank (ZMod 2) V = n) (hn : 3 ≤ n) (hrm : r.Monic)
    (hri : Irreducible r) (hrd : r.natDegree = n - 1) {u u' : GLV (ZMod 2) V}
    (hr : r ∣ minpoly (ZMod 2) (u : End)) (hr' : r ∣ minpoly (ZMod 2) (u' : End)) :
    IsConj u u' := by
  obtain ⟨v, hv⟩ := exists_cyclic hV hn hrm hri hrd hr
  obtain ⟨v', hv'⟩ := exists_cyclic hV hn hrm hri hrd hr'
  have hm0 : aeval (u : End) (r * (X + 1)) = 0 := by
    rw [← minpoly_eq_of_dvd hV hn hrm hri hrd hr]; exact minpoly.aeval _ _
  have hm0' : aeval (u' : End) (r * (X + 1)) = 0 := by
    rw [← minpoly_eq_of_dvd hV hn hrm hri hrd hr']; exact minpoly.aeval _ _
  obtain ⟨φ, hφ⟩ := exists_conj_of_cyclic (hrm.mul (monic_X_add_C 1))
    (natDegree_r_mul hn hrm hrd) hV hm0 hm0' hv hv'
  refine isConj_iff.2 ⟨GLV.ofEquiv φ, GLV.ext fun x => ?_⟩
  simp [hφ]
end ClassN

end Vaserstein
