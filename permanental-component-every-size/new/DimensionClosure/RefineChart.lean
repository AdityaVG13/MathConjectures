import DimensionClosure.DenseSmoothComponent

set_option autoImplicit false
universe u
namespace ComponentDimensionClosure
noncomputable section

theorem component_from_chart_and_seed
    (K A : Type u) [Field K] [CommRing A] [Algebra K A]
    [Algebra.FinitePresentation K A]
    (f det : A) (ev : A →+* K) (hf : ev f ≠ 0) (hdet : ev det ≠ 0)
    [Algebra.Smooth K (Localization.Away f)] (d : ℕ)
    (hdim : ∀ Q : Ideal (Localization.Away f), IsMinimalPrime Q →
      ringKrullDim (Localization.Away f ⧸ Q) = d) :
    ∃ P : Ideal A, IsMinimalPrime P ∧ ringKrullDim (A ⧸ P) = d ∧
      ∃ U : Set (PrimeSpectrum A),
        U = PrimeSpectrum.zeroLocus P ∩ (PrimeSpectrum.basicOpen (f*det) : Set (PrimeSpectrum A)) ∧
        U.Nonempty ∧ closure U = PrimeSpectrum.zeroLocus P ∧
        (∀ x ∈ U, x ∈ Algebra.smoothLocus K A ∧ det ∉ x.asIdeal) := by
  let S := Localization.Away f
  let g : S := algebraMap A S det
  let T := Localization.Away g
  let evS : S →+* K := IsLocalization.Away.lift f (isUnit_iff_ne_zero.mpr hf)
  have hg : evS g ≠ 0 := by
    simpa [evS,g] using hdet
  let evT : T →+* K := IsLocalization.Away.lift g (isUnit_iff_ne_zero.mpr hg)
  letI : Nontrivial T := evT.domain_nontrivial
  letI : Algebra.Smooth S T := Algebra.Smooth.of_isLocalization_Away g
  letI : Algebra.Smooth K T := Algebra.Smooth.comp K S T
  letI : IsLocalization.Away (f*det) T := IsLocalization.Away.mul' S T f det
  have hunit : IsUnit (algebraMap A T det) := by
    rw [IsScalarTower.algebraMap_apply A S T]
    exact IsLocalization.Away.algebraMap_isUnit g
  apply component_from_smooth_principal_chart K A T (f*det) det d hunit
  exact component_dimensions_localization K S T (Submonoid.powers g) d hdim

#print axioms component_from_chart_and_seed
end
end ComponentDimensionClosure
