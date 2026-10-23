import CanonicalProblem.ComponentTransport
import ActualLocalChart.ComponentClosure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
namespace ComponentCanonicalProblem
noncomputable section
open PrimeSpectrum

theorem component_from_equivalent_chart_and_seed
    (K A B : Type u) [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra.FinitePresentation K A]
    (e : A ≃ₐ[K] B) (f det : A) (ev : A →+* K)
    (hf : ev f ≠ 0) (hdet : ev det ≠ 0)
    [Algebra.Smooth K (Localization.Away f)] (d : ℕ)
    (hdim : ∀ Q : Ideal (Localization.Away f), IsMinimalPrime Q →
      ringKrullDim (Localization.Away f ⧸ Q) = d) :
    ∃ P : Ideal B, IsMinimalPrime P ∧ ringKrullDim (B ⧸ P) = d ∧
      zeroLocus (P : Set B) ∈ irreducibleComponents (PrimeSpectrum B) ∧
      ∃ U : Set (PrimeSpectrum B),
        U = zeroLocus P ∩ (basicOpen (e (f*det)) : Set (PrimeSpectrum B)) ∧
        U.Nonempty ∧ closure U = zeroLocus P ∧
        (∀ x ∈ U, x ∈ Algebra.smoothLocus K B ∧ e det ∉ x.asIdeal) := by
  let S := Localization.Away f
  let g : S := algebraMap A S det
  let T := Localization.Away g
  let evS : S →+* K := IsLocalization.Away.lift f (isUnit_iff_ne_zero.mpr hf)
  have hg : evS g ≠ 0 := by simpa [evS,g] using hdet
  let evT : T →+* K := IsLocalization.Away.lift g (isUnit_iff_ne_zero.mpr hg)
  letI : Nontrivial T := evT.domain_nontrivial
  letI : Algebra.Smooth S T := Algebra.Smooth.of_isLocalization_Away g
  letI : Algebra.Smooth K T := Algebra.Smooth.comp K S T
  letI : IsLocalization.Away (f*det) T := IsLocalization.Away.mul' S T f det
  have hunit : IsUnit (algebraMap A T det) := by
    rw [IsScalarTower.algebraMap_apply A S T]
    exact IsLocalization.Away.algebraMap_isUnit g
  apply component_from_equivalent_smooth_chart K A B T e (f*det) det d hunit
  exact ComponentDimensionClosure.component_dimensions_localization K S T (Submonoid.powers g) d hdim

open ComponentChartJacobian ComponentFullHessianRank ComponentActualLocalChart ComponentFamilyContainment

theorem groupedDeterminant_eq (k : ℕ) : groupedDeterminant k = quotientDeterminant k := by
  unfold groupedDeterminant quotientDeterminant actualDeterminant
  congr 1
  change (Matrix.submatrix (Matrix.fromBlocks (blockU k) (blockV k) (blockL k) (blockW k))
    (familyIndexEquiv k) (familyIndexEquiv k)).det = _
  unfold blockU
  rw [← actualAmbient_blocks, Matrix.det_submatrix_equiv_self]

theorem canonical_component_from_grouped_chart_and_seed
    (k : ℕ) (hk : 1 ≤ k) (f : ActualQuotient k) (hf : quotientSeedEval k f ≠ 0)
    [Algebra.Smooth ℂ (Localization.Away f)]
    (hdim : ∀ Q : Ideal (Localization.Away f), IsMinimalPrime Q →
      ringKrullDim (Localization.Away f ⧸ Q) = ((k^2+3*k+8 : ℕ) : WithBot ℕ∞)) :
    ∃ P : Ideal (CoordinateAlgebra k), IsMinimalPrime P ∧
      ringKrullDim (CoordinateAlgebra k ⧸ P) = ((k^2+3*k+8 : ℕ) : WithBot ℕ∞) ∧
      zeroLocus (P : Set (CoordinateAlgebra k)) ∈ irreducibleComponents (PrimeSpectrum (CoordinateAlgebra k)) ∧
      ∃ U : Set (PrimeSpectrum (CoordinateAlgebra k)),
        U = zeroLocus P ∩ (basicOpen (coordinateAlgebraEquiv k f * canonicalDeterminant k) :
          Set (PrimeSpectrum (CoordinateAlgebra k))) ∧
        U.Nonempty ∧ closure U = zeroLocus P ∧
        (∀ x ∈ U, x ∈ Algebra.smoothLocus ℂ (CoordinateAlgebra k) ∧ canonicalDeterminant k ∉ x.asIdeal) := by
  letI : Algebra.FinitePresentation ℂ (ActualQuotient k) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hd : quotientSeedEval k (groupedDeterminant k) ≠ 0 := by
    rw [groupedDeterminant_eq]
    exact quotientDeterminant_seed_ne_zero k hk
  have hh := component_from_equivalent_chart_and_seed ℂ (ActualQuotient k) (CoordinateAlgebra k)
    (coordinateAlgebraEquiv k) f (groupedDeterminant k) (quotientSeedEval k).toRingHom
    hf hd (k^2+3*k+8) hdim
  simpa only [map_mul, quotient_determinant_compatibility] using hh

#print axioms canonical_component_from_grouped_chart_and_seed
#print axioms groupedDeterminant_eq
end
end ComponentCanonicalProblem
