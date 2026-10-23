import AxisProjectionSetup
import MonomialBridge
import GeneratorExponents
import Mathlib.Algebra.MvPolynomial.Rename

namespace ConcreteLocalGeometry
open MvPolynomial

/-- The two variables retained by one axis projection. -/
abbrev AxisVars (k : Fin 16) := {i : Fin 16 // i = 0 ∨ i = k}

/-- The coordinate ideal killing all variables except x0 and xk. -/
noncomputable def axisIdeal (k : Fin 16) : Ideal P :=
  Ideal.span (MvPolynomial.X '' {i : Fin 16 | i ≠ 0 ∧ i ≠ k})

private theorem axisProjection_eq_rename_killCompl (k : Fin 16) :
    axisProjection k =
      (MvPolynomial.rename (Subtype.val : AxisVars k → Fin 16)).toRingHom.comp
        (MvPolynomial.killCompl (Subtype.val_injective :
          Function.Injective (Subtype.val : AxisVars k → Fin 16))).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [axisProjection]
  · intro i
    by_cases hi : i = 0 ∨ i = k
    · have hrename : MvPolynomial.rename (Subtype.val : AxisVars k → Fin 16)
          (MvPolynomial.X (⟨i, hi⟩ : AxisVars k) : MvPolynomial (AxisVars k) ℂ) =
          MvPolynomial.X i := by simp
      have hk := MvPolynomial.killCompl_rename_app
        (Subtype.val_injective : Function.Injective (Subtype.val : AxisVars k → Fin 16))
        (MvPolynomial.X (⟨i, hi⟩ : AxisVars k) : MvPolynomial (AxisVars k) ℂ)
      rw [hrename] at hk
      simp only [axisProjection, MvPolynomial.eval₂Hom_X', ite_eq_left hi,
        RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hk]
      simp [x]
    · have hrange : i ∉ Set.range (Subtype.val : AxisVars k → Fin 16) := by
        simpa using hi
      simp [axisProjection, hi, MvPolynomial.killCompl]

/-- An axis projection leaves every coefficient supported on its two retained
    variables unchanged. This uses mathlib's proved killCompl interface. -/
theorem coeff_axisProjection_of_support (k : Fin 16) (p : P)
    (d : Fin 16 →₀ ℕ)
    (hd : ∀ i ∈ d.support, i = 0 ∨ i = k) :
    (axisProjection k p).coeff d = p.coeff d := by
  classical
  let f : AxisVars k → Fin 16 := Subtype.val
  have hf : Function.Injective f := Subtype.val_injective
  have hs : (↑d.support : Set (Fin 16)) ⊆ Set.range f := by
    intro i hi
    exact ⟨⟨i, hd i hi⟩, rfl⟩
  have he : (d.comapDomain f hf.injOn).mapDomain f = d :=
    Finsupp.mapDomain_comapDomain f hf d hs
  rw [axisProjection_eq_rename_killCompl]
  change (MvPolynomial.rename f (MvPolynomial.killCompl hf p)).coeff d = p.coeff d
  rw [← he, MvPolynomial.coeff_rename_mapDomain f hf, MvPolynomial.coeff_killCompl]

/-- Vanishing on an axis forces every supported monomial to contain a killed
    variable. No degree truncation is used. -/
theorem axisProjection_zero_support (k : Fin 16) (p : P)
    (hp : axisProjection k p = 0) :
    ∀ d ∈ p.support, ∃ i : Fin 16, i ≠ 0 ∧ i ≠ k ∧ d i ≠ 0 := by
  classical
  intro d hd
  by_contra hn
  push Not at hn
  have hs : ∀ i ∈ d.support, i = 0 ∨ i = k := by
    intro i hi
    by_contra h
    push Not at h
    exact (Finsupp.mem_support_iff.mp hi) (hn i h.1 h.2)
  have hc := coeff_axisProjection_of_support k p d hs
  rw [hp, AddMonoidAlgebra.coeff_zero] at hc
  exact (MvPolynomial.mem_support_iff.mp hd) hc.symm

/-- The concrete axis substitution has precisely the expected coordinate ideal
    as its kernel. -/
theorem axisIdeal_eq_ker (k : Fin 16) : axisIdeal k = RingHom.ker (axisProjection k) := by
  apply le_antisymm
  · rw [axisIdeal, Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    apply RingHom.mem_ker.mpr
    simp [axisProjection, hi.1, hi.2]
  · intro p hp
    rw [axisIdeal, MvPolynomial.mem_ideal_span_X_image]
    intro d hd
    obtain ⟨i, hi0, hik, hdi⟩ := axisProjection_zero_support k p (RingHom.mem_ker.mp hp) d hd
    exact ⟨i, ⟨hi0, hik⟩, hdi⟩

/-- Identification of the actual target ideal with the generic monomial ideal. -/
theorem targetIdeal_eq_monomialIdeal :
    targetIdeal = LocalGeometryMonomial.monomialIdeal (R := ℂ) generatorExponent := by
  unfold targetIdeal LocalGeometryMonomial.monomialIdeal
  congr 1
  ext p
  simp only [Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, (targetGenerator_eq_monomial i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, targetGenerator_eq_monomial i⟩

private theorem error_exponent_dominates (d : Fin 16 →₀ ℕ) (i : Fin 16)
    (hi : 4 ≤ i.val) (hd : d i ≠ 0) :
    ∃ j, generatorExponent j ≤ d := by
  fin_cases i
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · refine ⟨(0 : Fin 15), ?_⟩
    change Finsupp.single (4 : Fin 16) 1 ≤ d
    exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hd)
  · refine ⟨(1 : Fin 15), ?_⟩
    change Finsupp.single (5 : Fin 16) 1 ≤ d
    exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hd)
  · refine ⟨(2 : Fin 15), ?_⟩
    change Finsupp.single (6 : Fin 16) 1 ≤ d
    exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hd)
  · refine ⟨(3 : Fin 15), ?_⟩
    change Finsupp.single (7 : Fin 16) 1 ≤ d
    exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hd)
  · refine ⟨(4 : Fin 15), ?_⟩
    change Finsupp.single (8 : Fin 16) 1 ≤ d
    exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hd)
  · refine ⟨(5 : Fin 15), ?_⟩
    change Finsupp.single (9 : Fin 16) 1 ≤ d
    exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hd)
  · refine ⟨(6 : Fin 15), ?_⟩
    change Finsupp.single (10 : Fin 16) 1 ≤ d
    exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hd)
  · refine ⟨(7 : Fin 15), ?_⟩
    change Finsupp.single (11 : Fin 16) 1 ≤ d
    exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hd)
  · refine ⟨(8 : Fin 15), ?_⟩
    change Finsupp.single (12 : Fin 16) 1 ≤ d
    exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hd)
  · refine ⟨(9 : Fin 15), ?_⟩
    change Finsupp.single (13 : Fin 16) 1 ≤ d
    exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hd)
  · refine ⟨(10 : Fin 15), ?_⟩
    change Finsupp.single (14 : Fin 16) 1 ≤ d
    exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hd)
  · refine ⟨(11 : Fin 15), ?_⟩
    change Finsupp.single (15 : Fin 16) 1 ≤ d
    exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hd)

/-- Exact classification of monomials killed by all three axis projections. -/
theorem exists_generatorExponent_le_of_axis_witnesses (d : Fin 16 →₀ ℕ)
    (h1 : ∃ i : Fin 16, i ≠ 0 ∧ i ≠ 1 ∧ d i ≠ 0)
    (h2 : ∃ i : Fin 16, i ≠ 0 ∧ i ≠ 2 ∧ d i ≠ 0)
    (h3 : ∃ i : Fin 16, i ≠ 0 ∧ i ≠ 3 ∧ d i ≠ 0) :
    ∃ j, generatorExponent j ≤ d := by
  classical
  by_cases he : ∃ i : Fin 16, 4 ≤ i.val ∧ d i ≠ 0
  · obtain ⟨i, hi, hdi⟩ := he
    exact error_exponent_dominates d i hi hdi
  push Not at he
  have h12 : d 1 ≠ 0 ∨ d 2 ≠ 0 := by
    obtain ⟨i, hi0, hi3, hdi⟩ := h3
    fin_cases i <;> simp_all
  have h13 : d 1 ≠ 0 ∨ d 3 ≠ 0 := by
    obtain ⟨i, hi0, hi2, hdi⟩ := h2
    fin_cases i <;> simp_all
  have h23 : d 2 ≠ 0 ∨ d 3 ≠ 0 := by
    obtain ⟨i, hi0, hi1, hdi⟩ := h1
    fin_cases i <;> simp_all
  have hpairs : (d 1 ≠ 0 ∧ d 2 ≠ 0) ∨
      (d 1 ≠ 0 ∧ d 3 ≠ 0) ∨ (d 2 ≠ 0 ∧ d 3 ≠ 0) := by tauto
  rcases hpairs with ⟨ha, hd⟩ | ⟨ha, hq⟩ | ⟨hd, hq⟩
  · refine ⟨(12 : Fin 15), ?_⟩
    change Finsupp.single (1 : Fin 16) 1 + Finsupp.single 2 1 ≤ d
    intro i
    fin_cases i <;> simp [Finsupp.single_apply, Nat.one_le_iff_ne_zero, ha, hd]
  · refine ⟨(13 : Fin 15), ?_⟩
    change Finsupp.single (1 : Fin 16) 1 + Finsupp.single 3 1 ≤ d
    intro i
    fin_cases i <;> simp [Finsupp.single_apply, Nat.one_le_iff_ne_zero, ha, hq]
  · refine ⟨(14 : Fin 15), ?_⟩
    change Finsupp.single (2 : Fin 16) 1 + Finsupp.single 3 1 ≤ d
    intro i
    fin_cases i <;> simp [Finsupp.single_apply, Nat.one_le_iff_ne_zero, hd, hq]

/-- Every polynomial vanishing identically on all three coordinate axes belongs
    to the actual target ideal; no truncation or empirical sampling is involved. -/
theorem mem_targetIdeal_of_axes_zero {p : P}
    (h1 : axisProjection 1 p = 0) (h2 : axisProjection 2 p = 0)
    (h3 : axisProjection 3 p = 0) : p ∈ targetIdeal := by
  rw [targetIdeal_eq_monomialIdeal, LocalGeometryMonomial.mem_monomialIdeal_iff]
  intro d hd
  exact exists_generatorExponent_le_of_axis_witnesses d
    (axisProjection_zero_support 1 p h1 d hd)
    (axisProjection_zero_support 2 p h2 d hd)
    (axisProjection_zero_support 3 p h3 d hd)

theorem targetIdeal_le_axisIdeal (k : Fin 16) (hk : k = 1 ∨ k = 2 ∨ k = 3) :
    targetIdeal ≤ axisIdeal k := by
  rw [axisIdeal_eq_ker, targetIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  apply RingHom.mem_ker.mpr
  rcases hk with rfl | rfl | rfl <;> fin_cases i <;>
    simp [axisProjection, targetGenerator, x]

/-- The target monomial ideal is exactly the intersection of the three
    coordinate ideals, scheme-theoretically. -/
theorem targetIdeal_eq_axes_intersection :
    targetIdeal = axisIdeal 1 ⊓ (axisIdeal 2 ⊓ axisIdeal 3) := by
  apply le_antisymm
  · exact le_inf (targetIdeal_le_axisIdeal 1 (by simp))
      (le_inf (targetIdeal_le_axisIdeal 2 (by simp)) (targetIdeal_le_axisIdeal 3 (by simp)))
  · intro p hp
    apply mem_targetIdeal_of_axes_zero
    · exact RingHom.mem_ker.mp ((axisIdeal_eq_ker 1) ▸ hp.1)
    · exact RingHom.mem_ker.mp ((axisIdeal_eq_ker 2) ▸ hp.2.1)
    · exact RingHom.mem_ker.mp ((axisIdeal_eq_ker 3) ▸ hp.2.2)

#print axioms coeff_axisProjection_of_support
#print axioms axisIdeal_eq_ker
#print axioms mem_targetIdeal_of_axes_zero
#print axioms targetIdeal_eq_axes_intersection
end ConcreteLocalGeometry
