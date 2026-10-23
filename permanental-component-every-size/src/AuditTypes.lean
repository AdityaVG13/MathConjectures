import ConcreteLocalStructure
namespace IndependentAudit
open ConcreteLocalGeometry
example : P = MvPolynomial (Fin 16) ℂ := rfl
example : origin = RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun _ : Fin 16 => 0)) := rfl
example : Local = Localization.AtPrime origin := rfl
example (ij : Fin 5 × Fin 5) : equation ij = (N.submatrix ij.1.succAbove ij.2.succAbove).permanent := rfl
example : localCritical = localTarget := ConcreteLocalGeometry.localCritical_eq_localTarget
example : localCritical = localAxisIdeal 1 ⊓ (localAxisIdeal 2 ⊓ localAxisIdeal 3) := ConcreteLocalGeometry.localCritical_eq_three_primes
example : localCritical.IsRadical := ConcreteLocalGeometry.localCritical_isRadical
example : (localAxisIdeal 1).IsPrime := localAxisIdeal_isPrime 1
example : (localAxisIdeal 2).IsPrime := localAxisIdeal_isPrime 2
example : (localAxisIdeal 3).IsPrime := localAxisIdeal_isPrime 3
end IndependentAudit
set_option pp.all true in
#check @ConcreteLocalGeometry.localCritical_eq_localTarget
#print ConcreteLocalGeometry.localCritical_eq_localTarget
#print axioms ConcreteLocalGeometry.localCritical_eq_localTarget
#print axioms ConcreteLocalGeometry.localCritical_eq_three_primes
#print axioms ConcreteLocalGeometry.localCritical_isRadical
#print axioms ConcreteLocalGeometry.three_localAxisIdeals_incomparable
