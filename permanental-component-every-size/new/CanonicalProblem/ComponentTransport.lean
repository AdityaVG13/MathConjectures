import CanonicalProblem.CoordinateEquivalence
import DimensionClosure.DenseSmoothComponent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
namespace ComponentCanonicalProblem
open PrimeSpectrum

/-- Transport a certified smooth principal chart across an algebra equivalence,
then construct the component in the target spectrum itself. No component
existence is assumed. The chart ring and all its component dimensions are
unchanged; only the base algebra structure is transported. -/
theorem component_from_equivalent_smooth_chart
    (K A B S : Type u) [Field K] [CommRing A] [CommRing B] [CommRing S] [Nontrivial S]
    [Algebra K A] [Algebra K B] [Algebra K S] [Algebra A S] [IsScalarTower K A S]
    [Algebra.FinitePresentation K A] [Algebra.Smooth K S]
    (e : A ≃ₐ[K] B) (f det : A) [IsLocalization.Away f S] (d : ℕ)
    (hdet : IsUnit (algebraMap A S det))
    (hdim : ∀ Q : Ideal S, IsMinimalPrime Q → ringKrullDim (S ⧸ Q) = d) :
    ∃ P : Ideal B, IsMinimalPrime P ∧ ringKrullDim (B ⧸ P) = d ∧
      zeroLocus (P : Set B) ∈ irreducibleComponents (PrimeSpectrum B) ∧
      ∃ U : Set (PrimeSpectrum B),
        U = zeroLocus P ∩ (basicOpen (e f) : Set (PrimeSpectrum B)) ∧
        U.Nonempty ∧ closure U = zeroLocus P ∧
        (∀ x ∈ U, x ∈ Algebra.smoothLocus K B ∧ e det ∉ x.asIdeal) := by
  letI : Algebra B S := ((algebraMap A S).comp e.symm.toRingHom).toAlgebra
  haveI : IsScalarTower K B S := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap K S x = algebraMap A S (e.symm (algebraMap K B x))
    rw [e.symm.commutes]
    exact IsScalarTower.algebraMap_apply K A S x
  haveI : Algebra.FinitePresentation K B := Algebra.FinitePresentation.equiv e
  haveI : IsLocalization.Away (e f) S := by
    have hi := IsLocalization.isLocalization_of_base_ringEquiv (Submonoid.powers f) S e.toRingEquiv
    simp only [Submonoid.map_powers] at hi
    convert hi using 1
  have hdet' : IsUnit (algebraMap B S (e det)) := by
    change IsUnit (algebraMap A S (e.symm (e det)))
    simpa using hdet
  obtain ⟨P,hP,hd,U,hU,hne,hcl,hsm⟩ :=
    ComponentDimensionClosure.component_from_smooth_principal_chart K B S (e f) (e det) d hdet' hdim
  exact ⟨P,hP,hd,ComponentDimensionClosure.minimalPrime_is_component P hP,U,hU,hne,hcl,hsm⟩

noncomputable section
open ComponentChartJacobian ComponentFullHessianRank ComponentActualLocalChart
abbrev GroupedCoordinateAlgebra (k : ℕ) := P k ⧸ actualGradientIdeal k

def groupedDeterminant (k : ℕ) : GroupedCoordinateAlgebra k :=
  Ideal.Quotient.mk (actualGradientIdeal k) (finiteAmbient k).det

def canonicalDeterminant (k : ℕ) : CoordinateAlgebra k :=
  Ideal.Quotient.mk (cofactorIdeal k) (genericMatrix k).det

theorem quotient_determinant_compatibility (k : ℕ) :
    coordinateAlgebraEquiv k (groupedDeterminant k) = canonicalDeterminant k := by
  change Ideal.Quotient.mk (cofactorIdeal k) (coordinateEquiv k (finiteAmbient k).det) = _
  rw [determinant_compatibility]
  rfl

/-- Concrete canonical conclusion from a certified chart of the grouped actual
coordinate algebra. Every conclusion is on the standard independent-entry
cofactor quotient, and determinant nonvanishing uses its genuine determinant. -/
theorem canonical_component_from_grouped_chart
    (k : ℕ) (S : Type) [CommRing S] [Nontrivial S]
    [Algebra ℂ S] [Algebra (GroupedCoordinateAlgebra k) S]
    [IsScalarTower ℂ (GroupedCoordinateAlgebra k) S]
    [Algebra.FinitePresentation ℂ (GroupedCoordinateAlgebra k)] [Algebra.Smooth ℂ S]
    (f : GroupedCoordinateAlgebra k) [IsLocalization.Away f S] (d : ℕ)
    (hdet : IsUnit (algebraMap (GroupedCoordinateAlgebra k) S (groupedDeterminant k)))
    (hdim : ∀ Q : Ideal S, IsMinimalPrime Q → ringKrullDim (S ⧸ Q) = d) :
    ∃ P : Ideal (CoordinateAlgebra k), IsMinimalPrime P ∧
      ringKrullDim (CoordinateAlgebra k ⧸ P) = d ∧
      zeroLocus (P : Set (CoordinateAlgebra k)) ∈ irreducibleComponents (PrimeSpectrum (CoordinateAlgebra k)) ∧
      ∃ U : Set (PrimeSpectrum (CoordinateAlgebra k)),
        U = zeroLocus P ∩ (basicOpen (coordinateAlgebraEquiv k f) : Set (PrimeSpectrum (CoordinateAlgebra k))) ∧
        U.Nonempty ∧ closure U = zeroLocus P ∧
        (∀ x ∈ U, x ∈ Algebra.smoothLocus ℂ (CoordinateAlgebra k) ∧ canonicalDeterminant k ∉ x.asIdeal) := by
  have hh := component_from_equivalent_smooth_chart ℂ (GroupedCoordinateAlgebra k)
    (CoordinateAlgebra k) S (coordinateAlgebraEquiv k) f (groupedDeterminant k) d hdet hdim
  simpa only [quotient_determinant_compatibility] using hh

end
#print axioms canonical_component_from_grouped_chart
#print axioms quotient_determinant_compatibility
#print axioms component_from_equivalent_smooth_chart
end ComponentCanonicalProblem
