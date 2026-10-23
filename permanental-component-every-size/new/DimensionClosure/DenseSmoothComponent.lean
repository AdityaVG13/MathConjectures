import DimensionClosure.LocalizedComponents
import Mathlib.RingTheory.Smooth.Locus

set_option autoImplicit false
universe u
namespace ComponentDimensionClosure
open PrimeSpectrum

theorem minimalPrime_is_component {A : Type*} [CommRing A]
    (P : Ideal A) (hP : IsMinimalPrime P) :
    zeroLocus (P : Set A) ∈ irreducibleComponents (PrimeSpectrum A) := by
  apply zeroLocus_ideal_mem_irreducibleComponents.mpr
  rw [hP.isPrime.radical]
  exact hP

/-- A nonempty smooth principal chart with known component dimensions produces
an actual ambient component with a dense smooth open locus and an additional unit condition.
The concrete application must supply the actual chart algebra and its dimension proof. -/
theorem component_from_smooth_principal_chart
    (K A S : Type u) [Field K] [CommRing A] [CommRing S] [Nontrivial S]
    [Algebra K A] [Algebra K S] [Algebra A S] [IsScalarTower K A S]
    [Algebra.FinitePresentation K A] [Algebra.Smooth K S]
    (f det : A) [IsLocalization.Away f S] (d : ℕ)
    (hdet : IsUnit (algebraMap A S det))
    (hdim : ∀ Q : Ideal S, IsMinimalPrime Q → ringKrullDim (S ⧸ Q) = d) :
    ∃ P : Ideal A, IsMinimalPrime P ∧ ringKrullDim (A ⧸ P) = d ∧
      ∃ U : Set (PrimeSpectrum A),
        U = zeroLocus P ∩ (basicOpen f : Set (PrimeSpectrum A)) ∧
        U.Nonempty ∧ closure U = zeroLocus P ∧
        (∀ x ∈ U, x ∈ Algebra.smoothLocus K A ∧ det ∉ x.asIdeal) := by
  obtain ⟨P,hP,hd,hpd⟩ := exists_component_from_chart K A S (Submonoid.powers f) d hdim
  haveI : P.IsPrime := hP.isPrime
  have hfP : f ∉ P := by
    intro hf
    exact Set.disjoint_left.mp hd (show f ∈ (Submonoid.powers f : Set A) from ⟨1, by simp⟩) hf
  let p : PrimeSpectrum A := ⟨P,inferInstance⟩
  let U : Set (PrimeSpectrum A) := zeroLocus P ∩ (basicOpen f : Set (PrimeSpectrum A))
  have hpU : p ∈ U := by
    constructor
    · change P ≤ P
      exact le_rfl
    · exact hfP
  have hcl : closure U = zeroLocus P := by
    apply le_antisymm (closure_minimal (show U ⊆ zeroLocus (P : Set A) from Set.inter_subset_left)
      (isClosed_zeroLocus (P : Set A)))
    rw [← closure_singleton p]
    apply closure_mono
    exact Set.singleton_subset_iff.mpr hpU
  let e : S ≃ₐ[K] Localization.Away f :=
    (IsLocalization.algEquiv (Submonoid.powers f) S (Localization.Away f)).restrictScalars K
  haveI : Algebra.Smooth K (Localization.Away f) := Algebra.Smooth.of_equiv e
  have hsm : (basicOpen f : Set (PrimeSpectrum A)) ⊆ Algebra.smoothLocus K A :=
    Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr inferInstance
  refine ⟨P,hP,hpd,U,rfl,⟨p,hpU⟩,hcl,?_⟩
  intro x hx
  refine ⟨hsm hx.2, ?_⟩
  intro hmem
  obtain ⟨n,hn⟩ := (IsLocalization.Away.algebraMap_isUnit_iff (S := S) (x := f)).mp hdet
  have hpow : f^n ∈ x.asIdeal := Ideal.mem_of_dvd x.asIdeal hn hmem
  exact hx.2 (x.isPrime.mem_of_pow_mem n hpow)

#print axioms component_from_smooth_principal_chart
end ComponentDimensionClosure
