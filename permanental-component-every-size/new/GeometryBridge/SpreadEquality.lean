import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Finiteness.Ideal

namespace UniformComponentGeometry
noncomputable section

/-- Finitely generated ideal containment at a prime has a single denominator. -/
theorem exists_multiplier_of_local_ideal_le
    {R : Type*} [CommRing R] (I J p : Ideal R) [p.IsPrime] (hI : I.FG)
    (h : I.map (algebraMap R (Localization.AtPrime p)) ≤
      J.map (algebraMap R (Localization.AtPrime p))) :
    ∃ s ∉ p, ∀ x ∈ I, s * x ∈ J := by
  classical
  obtain ⟨t, ht⟩ := hI
  have hx (x : t) : ∃ s : R, s ∈ p.primeCompl ∧ s * (x : R) ∈ J := by
    apply (IsLocalization.algebraMap_mem_map_algebraMap_iff
      p.primeCompl (Localization.AtPrime p) J x).mp
    apply h
    apply Ideal.mem_map_of_mem
    rw [← ht]
    exact Ideal.subset_span x.property
  choose d hd hdJ using hx
  let s : R := ∏ x : t, d x
  have hs : s ∈ p.primeCompl := p.primeCompl.prod_mem (fun x _ => hd x)
  refine ⟨s, hs, ?_⟩
  have hle : I ≤ Submodule.comap (LinearMap.mulLeft R s) (J : Submodule R R) := by
    rw [← ht]
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨a, ha⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ (⟨x,hx⟩ : t))
    change s * x ∈ J
    change s = d ⟨x,hx⟩ * a at ha
    rw [ha, mul_assoc, mul_comm a x, ← mul_assoc]
    exact J.mul_mem_right a (hdJ ⟨x,hx⟩)
  exact fun x hx => hle hx

/-- A common multiplier becomes ideal containment wherever it is a unit. -/
theorem ideal_map_le_of_multiplier
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (I J : Ideal R) (s : R) (hs : IsUnit (f s))
    (h : ∀ x ∈ I, s*x ∈ J) : I.map f ≤ J.map f := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  change f x ∈ J.map f
  apply (Ideal.unit_mul_mem_iff_mem _ hs).mp
  rw [← map_mul]
  exact Ideal.mem_map_of_mem f (h x hx)

/-- Equality of finitely generated ideals in a local ring spreads to a principal
open containing the given prime. This is scheme-theoretic ideal equality. -/
theorem exists_away_ideal_eq_of_atPrime_eq
    {R : Type*} [CommRing R] (I J p : Ideal R) [p.IsPrime]
    (hI : I.FG) (hJ : J.FG)
    (h : I.map (algebraMap R (Localization.AtPrime p)) =
      J.map (algebraMap R (Localization.AtPrime p))) :
    ∃ s ∉ p, I.map (algebraMap R (Localization.Away s)) =
      J.map (algebraMap R (Localization.Away s)) := by
  obtain ⟨a, ha, hIJ⟩ := exists_multiplier_of_local_ideal_le I J p hI h.le
  obtain ⟨b, hb, hJI⟩ := exists_multiplier_of_local_ideal_le J I p hJ h.ge
  refine ⟨a*b, p.primeCompl.mul_mem ha hb, ?_⟩
  have hu : IsUnit (algebraMap R (Localization.Away (a*b)) (a*b)) :=
    IsLocalization.map_units _ (⟨a*b, Submonoid.mem_powers (a*b)⟩ : Submonoid.powers (a*b))
  rw [map_mul] at hu
  exact le_antisymm
    (ideal_map_le_of_multiplier _ I J a (isUnit_of_mul_isUnit_left hu) hIJ)
    (ideal_map_le_of_multiplier _ J I b (isUnit_of_mul_isUnit_right hu) hJI)

end
end UniformComponentGeometry
