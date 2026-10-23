import GeometryBridge.IntegralDimension
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic

set_option autoImplicit false
universe u
namespace ComponentDimensionClosure
open Algebra

/-- Actual Krull dimension agrees with transcendence degree for a finite-type domain.
Noether normalization is supplied by mathlib, not assumed as an extra axiom. -/
theorem finiteType_dimension (K R : Type u) [Field K] [CommRing R] [IsDomain R]
    [Algebra K R] [Algebra.FiniteType K R] :
    ringKrullDim R = (Algebra.trdeg K R).toNat := by
  obtain ⟨n,g,hg,hint⟩ := exists_integral_inj_algHom_of_fg K R
  have hd : ringKrullDim R = n :=
    UniformComponentGeometry.ringKrullDim_eq_nat_of_integral_polynomial n g.toRingHom hint hg
  letI : Algebra (MvPolynomial (Fin n) K) R := g.toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin n) K) R :=
    IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  haveI : FaithfulSMul (MvPolynomial (Fin n) K) R :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  haveI : Algebra.IsIntegral (MvPolynomial (Fin n) K) R := ⟨hint⟩
  have ht : Algebra.trdeg K R = n := by
    rw [← trdeg_add_eq K (MvPolynomial (Fin n) K) (A := R), trdeg_eq_zero (R := MvPolynomial (Fin n) K) (A := R),
      add_zero, MvPolynomial.trdeg_of_isDomain]
    simp
  rw [hd, ht]
  simp

/-- Dense finite-type localizations of a finite-type domain preserve Krull dimension.
In applications S is the actual principal-open chart of an irreducible component. -/
theorem localization_dimension (K R S : Type u) [Field K] [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra K R] [Algebra K S] [Algebra R S]
    [IsScalarTower K R S] [Algebra.FiniteType K R] [Algebra.FiniteType K S]
    (M : Submonoid R) [IsLocalization M S]
    (hinj : Function.Injective (algebraMap R S)) : ringKrullDim S = ringKrullDim R := by
  letI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  letI : Algebra.IsAlgebraic R S := IsLocalization.isAlgebraic S M
  have ht : Algebra.trdeg K S = Algebra.trdeg K R := by
    rw [← trdeg_add_eq K R (A := S), trdeg_eq_zero (R := R) (A := S), add_zero]
  rw [finiteType_dimension K S, finiteType_dimension K R, ht]

#print axioms finiteType_dimension
#print axioms localization_dimension
end ComponentDimensionClosure
