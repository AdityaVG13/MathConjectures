import AxisIdealConsequences
import Mathlib.RingTheory.Localization.Ideal

/-!
# The target ideal in the genuine origin localization

These statements concern the actual target ideal J in P = C[X0,...,X15]
and its extension to Localization.AtPrime origin. They do not assume or
prove equality with the permanent-generated critical ideal.

The three coordinate planes retain X0 and respectively X1, X2, X3.
No dimension, regularity, or coordinate-normalization claim is made here.
-/

namespace ConcreteLocalGeometry

/-- Extension of an actual coordinate-plane ideal to the origin localization. -/
noncomputable def localAxisIdeal (k : Fin 16) : Ideal Local :=
  Ideal.map (algebraMap P Local) (axisIdeal k)

/-- Every coordinate-plane ideal is contained in the proved origin maximal ideal. -/
theorem axisIdeal_le_origin (k : Fin 16) : axisIdeal k ≤ origin := by
  rw [axisIdeal, Ideal.span_le]
  rintro _ ⟨i, _, rfl⟩
  apply RingHom.mem_ker.mpr
  simp [evalOrigin]

/-- No denominator in the origin prime complement belongs to an axis ideal. -/
theorem axisIdeal_disjoint_origin_complement (k : Fin 16) :
    Disjoint (origin.primeCompl : Set P) (axisIdeal k : Set P) := by
  apply Set.disjoint_left.mpr
  intro p hpM hpI
  exact hpM (axisIdeal_le_origin k hpI)

/-- Each of the extended coordinate-plane ideals is still prime. -/
theorem localAxisIdeal_isPrime (k : Fin 16) : (localAxisIdeal k).IsPrime := by
  exact IsLocalization.isPrime_of_isPrime_disjoint origin.primeCompl Local
    (axisIdeal k) (axisIdeal_isPrime k) (axisIdeal_disjoint_origin_complement k)

/-- In particular, none of the coordinate-plane ideals disappears under localization. -/
theorem localAxisIdeal_ne_top (k : Fin 16) : localAxisIdeal k ≠ ⊤ :=
  (localAxisIdeal_isPrime k).ne_top

/-- Contraction recovers exactly the original prime ideal. -/
theorem localAxisIdeal_under (k : Fin 16) : (localAxisIdeal k).under P = axisIdeal k := by
  exact IsLocalization.under_map_of_isPrime_disjoint origin.primeCompl Local
    (axisIdeal_isPrime k) (axisIdeal_disjoint_origin_complement k)

/-- Localization preserves this exact finite ideal intersection. -/
theorem localTarget_eq_axes_intersection :
    localTarget = localAxisIdeal 1 ⊓ (localAxisIdeal 2 ⊓ localAxisIdeal 3) := by
  unfold localTarget
  rw [targetIdeal_eq_axes_intersection,
    IsLocalization.map_inf origin.primeCompl Local,
    IsLocalization.map_inf origin.primeCompl Local]
  rfl

/-- The actual localized target ideal is radical, not just its finite jet. -/
theorem localTarget_isRadical : localTarget.IsRadical := by
  rw [localTarget_eq_axes_intersection]
  exact (localAxisIdeal_isPrime 1).isRadical.inf
    ((localAxisIdeal_isPrime 2).isRadical.inf (localAxisIdeal_isPrime 3).isRadical)

/-- The variable X_l separates the coordinate ideal killing it from the one retaining it. -/
theorem axisIdeal_not_le (k l : Fin 16) (hl : l ≠ 0) (hkl : k ≠ l) :
    ¬ axisIdeal k ≤ axisIdeal l := by
  intro h
  have hm : x l ∈ axisIdeal k := by
    exact Ideal.subset_span ⟨l, ⟨hl, Ne.symm hkl⟩, rfl⟩
  have hz := h hm
  rw [axisIdeal_eq_ker] at hz
  have hz' := RingHom.mem_ker.mp hz
  simpa [axisProjection, x] using hz'

/-- The noncontainment survives localization, by exact contraction. -/
theorem localAxisIdeal_not_le (k l : Fin 16) (hl : l ≠ 0) (hkl : k ≠ l) :
    ¬ localAxisIdeal k ≤ localAxisIdeal l := by
  intro h
  have hc := Ideal.comap_mono (f := algebraMap P Local) h
  change (localAxisIdeal k).under P ≤ (localAxisIdeal l).under P at hc
  rw [localAxisIdeal_under, localAxisIdeal_under] at hc
  exact axisIdeal_not_le k l hl hkl hc

/-- Any two distinct nonzero coordinate axes give incomparable localized prime ideals. -/
theorem localAxisIdeals_incomparable (k l : Fin 16)
    (hk : k ≠ 0) (hl : l ≠ 0) (hkl : k ≠ l) :
    (¬ localAxisIdeal k ≤ localAxisIdeal l) ∧
      (¬ localAxisIdeal l ≤ localAxisIdeal k) :=
  ⟨localAxisIdeal_not_le k l hl hkl, localAxisIdeal_not_le l k hk hkl.symm⟩

/-- An explicit finite specialization for the three branches. -/
theorem three_localAxisIdeals_incomparable :
    (¬ localAxisIdeal 1 ≤ localAxisIdeal 2) ∧
    (¬ localAxisIdeal 2 ≤ localAxisIdeal 1) ∧
    (¬ localAxisIdeal 1 ≤ localAxisIdeal 3) ∧
    (¬ localAxisIdeal 3 ≤ localAxisIdeal 1) ∧
    (¬ localAxisIdeal 2 ≤ localAxisIdeal 3) ∧
    (¬ localAxisIdeal 3 ≤ localAxisIdeal 2) := by
  exact ⟨localAxisIdeal_not_le 1 2 (by decide) (by decide),
    localAxisIdeal_not_le 2 1 (by decide) (by decide),
    localAxisIdeal_not_le 1 3 (by decide) (by decide),
    localAxisIdeal_not_le 3 1 (by decide) (by decide),
    localAxisIdeal_not_le 2 3 (by decide) (by decide),
    localAxisIdeal_not_le 3 2 (by decide) (by decide)⟩

end ConcreteLocalGeometry

#print axioms ConcreteLocalGeometry.axisIdeal_le_origin
#print axioms ConcreteLocalGeometry.localAxisIdeal_isPrime
#print axioms ConcreteLocalGeometry.localAxisIdeal_ne_top
#print axioms ConcreteLocalGeometry.localAxisIdeal_under
#print axioms ConcreteLocalGeometry.localTarget_eq_axes_intersection
#print axioms ConcreteLocalGeometry.localTarget_isRadical
#print axioms ConcreteLocalGeometry.localAxisIdeals_incomparable
#print axioms ConcreteLocalGeometry.three_localAxisIdeals_incomparable
