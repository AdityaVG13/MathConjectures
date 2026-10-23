import DimensionClosure.ComponentChart
import Mathlib.RingTheory.Spectrum.Prime.Topology

set_option autoImplicit false
universe u
namespace ComponentDimensionClosure

 theorem localized_minimalPrime_dimension
    (K A S : Type u) [Field K] [CommRing A] [CommRing S]
    [Algebra K A] [Algebra K S] [Algebra A S] [IsScalarTower K A S]
    [Algebra.FiniteType K A] [Algebra.FiniteType K S]
    (M : Submonoid A) [IsLocalization M S] (Q : Ideal S) (hQ : IsMinimalPrime Q) :
    IsMinimalPrime (Q.under A) ∧
    Disjoint (M : Set A) (Q.under A : Set A) ∧
    ringKrullDim (S ⧸ Q) = ringKrullDim (A ⧸ Q.under A) := by
  have hP : IsMinimalPrime (Q.under A) := by
    have hh : Q ∈ ((⊥ : Ideal A).map (algebraMap A S)).minimalPrimes := by
      simpa using hQ
    rw [IsLocalization.minimalPrimes_map M S (⊥ : Ideal A)] at hh
    exact hh
  haveI : Q.IsPrime := hQ.isPrime
  haveI : (Q.under A).IsPrime := hP.isPrime
  have hd : Disjoint (M : Set A) (Q.under A : Set A) :=
    (IsLocalization.disjoint_under_iff M S Q).mpr Ideal.IsPrime.ne_top'
  refine ⟨hP, hd, ?_⟩
  have he := prime_quotient_localization_dimension K A S M (Q.under A) hd
  rwa [IsLocalization.map_under M S Q] at he

/-- A component in a nonempty finite-type chart produces an actual ambient
minimal-prime component of the same Krull dimension. -/
theorem exists_component_from_chart
    (K A S : Type u) [Field K] [CommRing A] [CommRing S] [Nontrivial S]
    [Algebra K A] [Algebra K S] [Algebra A S] [IsScalarTower K A S]
    [Algebra.FiniteType K A] [Algebra.FiniteType K S]
    (M : Submonoid A) [IsLocalization M S] (d : ℕ)
    (hdim : ∀ Q : Ideal S, IsMinimalPrime Q → ringKrullDim (S ⧸ Q) = d) :
    ∃ P : Ideal A, IsMinimalPrime P ∧ Disjoint (M : Set A) (P : Set A) ∧
      ringKrullDim (A ⧸ P) = d := by
  obtain ⟨N,hN⟩ := Ideal.exists_maximal (α := S)
  letI : N.IsMaximal := hN
  obtain ⟨Q,hQ,_⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S)) (J := N) bot_le
  obtain ⟨hP,hd,he⟩ := localized_minimalPrime_dimension K A S M Q hQ
  exact ⟨Q.under A,hP,hd,he.symm.trans (hdim Q hQ)⟩

theorem component_dimensions_localization
    (K A S : Type u) [Field K] [CommRing A] [CommRing S]
    [Algebra K A] [Algebra K S] [Algebra A S] [IsScalarTower K A S]
    [Algebra.FiniteType K A] [Algebra.FiniteType K S]
    (M : Submonoid A) [IsLocalization M S] (d : ℕ)
    (hdim : ∀ P : Ideal A, IsMinimalPrime P → ringKrullDim (A ⧸ P) = d)
    (Q : Ideal S) (hQ : IsMinimalPrime Q) : ringKrullDim (S ⧸ Q) = d := by
  obtain ⟨hP,_,he⟩ := localized_minimalPrime_dimension K A S M Q hQ
  exact he.trans (hdim (Q.under A) hP)

#print axioms component_dimensions_localization
#print axioms localized_minimalPrime_dimension
#print axioms exists_component_from_chart
end ComponentDimensionClosure
