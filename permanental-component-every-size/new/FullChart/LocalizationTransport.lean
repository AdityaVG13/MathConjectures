import FullChart.Equivalence
import FullChart.FinTarget
import Mathlib.RingTheory.MvPolynomial.Localization
set_option backward.isDefEq.respectTransparency false
namespace UniformFullChart
noncomputable section
open MvPolynomial

section Generic
variable {R B S : Type*} [CommRing R] [CommRing B] [CommRing S]
  [Algebra ℂ R] [Algebra ℂ B] [Algebra ℂ S]
variable {σ : Type*} (e : R ≃ₐ[ℂ] MvPolynomial σ B) (d : B)
  [Algebra B S] [IsScalarTower ℂ B S] [IsLocalization.Away d S]
attribute [local instance] MvPolynomial.algebraMvPolynomial

def liftedDenominator : R := e.symm (C d)

instance polynomialCoefficientTower : IsScalarTower ℂ (MvPolynomial σ B) (MvPolynomial σ S) :=
  IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := MvPolynomial σ B) (A := MvPolynomial σ S) (by
    apply RingHom.ext
    intro z
    change C (algebraMap ℂ S z) =
      MvPolynomial.map (algebraMap B S) (C (algebraMap ℂ B z))
    rw [MvPolynomial.map_C,IsScalarTower.algebraMap_apply ℂ B S])

instance polynomialCoefficientLocalization :
    IsLocalization.Away (C d : MvPolynomial σ B) (MvPolynomial σ S) := by
  simpa only [Submonoid.map_powers] using
    (inferInstance : IsLocalization ((Submonoid.powers d).map
      (C : B →+* MvPolynomial σ B)) (MvPolynomial σ S))

/-- Transport a coefficient-ring localization through an actual polynomial chart. -/
def liftCoefficientLocalization :
    Localization.Away (liftedDenominator e d) ≃ₐ[ℂ] MvPolynomial σ S :=
  IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers (liftedDenominator e d))
    (T := Submonoid.powers (C d : MvPolynomial σ B))
    _ _ e (by rw [Submonoid.map_powers]; simp [liftedDenominator])

end Generic

/-- The ambient L/V elimination chart can be further localized along any
coefficient denominator, with no assumed coordinate decomposition. -/
def ambientCoefficientLocalization (k : ℕ) (d : Base k) :
    Localization.Away (liftedDenominator (eliminationAlgEquiv k) d) ≃ₐ[ℂ]
      MvPolynomial (Fin k) (Localization.Away d) :=
  liftCoefficientLocalization (S := Localization.Away d) (eliminationAlgEquiv k) d

#print axioms ambientCoefficientLocalization
end
end UniformFullChart
