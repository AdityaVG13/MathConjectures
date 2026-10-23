import DimensionClosure.FiniteTypeDimension
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

set_option autoImplicit false
universe u
namespace ComponentDimensionClosure

/-- An irreducible finite-type component and any nonempty finite-type localization
of that component have the same actual Krull dimension. -/
theorem prime_quotient_localization_dimension
    (K A S : Type u) [Field K] [CommRing A] [CommRing S]
    [Algebra K A] [Algebra K S] [Algebra A S] [IsScalarTower K A S]
    [Algebra.FiniteType K A] [Algebra.FiniteType K S]
    (M : Submonoid A) [IsLocalization M S] (P : Ideal A) [P.IsPrime]
    (hd : Disjoint (M : Set A) (P : Set A)) :
    ringKrullDim (S ⧸ P.map (algebraMap A S)) = ringKrullDim (A ⧸ P) := by
  letI : (P.map (algebraMap A S)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M S P inferInstance hd
  have hu : (P.map (algebraMap A S)).under A = P :=
    IsLocalization.under_map_of_isPrime_disjoint M S inferInstance hd
  haveI : IsScalarTower K (A ⧸ P) (S ⧸ P.map (algebraMap A S)) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change Ideal.Quotient.mk _ (algebraMap K S x) =
        Ideal.Quotient.mk _ (algebraMap A S (algebraMap K A x))
      rw [IsScalarTower.algebraMap_apply K A S])
  apply localization_dimension K (A ⧸ P) (S ⧸ P.map (algebraMap A S))
    (Algebra.algebraMapSubmonoid (A ⧸ P) M)
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hm : algebraMap A S a ∈ P.map (algebraMap A S) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hx
  have hm' : a ∈ (P.map (algebraMap A S)).under A := hm
  rwa [hu] at hm'

#print axioms prime_quotient_localization_dimension
end ComponentDimensionClosure
