import ConcreteLocalSetup
import GeneratorExponents
import MonomialBridge
import LocalNakayama

/-!
# Conditional localization assembly for the actual polynomial ideals

The ring, origin ideal, fifteen target generators, and localized ideals are
the actual objects from `ConcreteLocalSetup`. Their finite generation and the
local Jacobson-radical containment below are proved, not additional inputs.

The final theorem in this file remains conditional on two global polynomial
ideal statements. It does not claim their verification or the unconditional
concrete local equality.
-/

namespace ConcreteLocalGeometry

/-- The actual target has its displayed finite generating set. -/
theorem targetIdeal_fg : targetIdeal.FG := by
  exact Submodule.fg_span (Set.finite_range targetGenerator)

/-- Extension to the actual local ring preserves the displayed finite
spanning set, with no global Noetherianity premise. -/
theorem localTarget_fg : localTarget.FG := by
  rw [localTarget, targetIdeal, Ideal.map_span]
  exact Submodule.fg_span ((Set.finite_range targetGenerator).image (algebraMap P Local))

/-- Every variable vanishes at the origin defining the localization. -/
theorem idealOfVars_le_origin : MvPolynomial.idealOfVars (Fin 16) ℂ ≤ origin := by
  rw [MvPolynomial.idealOfVars, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change evalOrigin (MvPolynomial.X i) = 0
  simp [evalOrigin]

/-- The extended variable ideal lies in the genuine local maximal ideal. -/
theorem map_idealOfVars_le_local_maximal :
    Ideal.map (algebraMap P Local) (MvPolynomial.idealOfVars (Fin 16) ℂ) ≤
      IsLocalRing.maximalIdeal Local := by
  calc
    Ideal.map (algebraMap P Local) (MvPolynomial.idealOfVars (Fin 16) ℂ) ≤
        Ideal.map (algebraMap P Local) origin := Ideal.map_mono idealOfVars_le_origin
    _ = IsLocalRing.maximalIdeal Local := Localization.AtPrime.map_eq_maximalIdeal

/-- Consequently the extended variable ideal lies in the Jacobson radical
required by the proved Nakayama containment criterion. -/
theorem map_idealOfVars_le_local_jacobson :
    Ideal.map (algebraMap P Local) (MvPolynomial.idealOfVars (Fin 16) ℂ) ≤
      Ideal.jacobson (⊥ : Ideal Local) :=
  map_idealOfVars_le_local_maximal.trans
    (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal Local))

/-- Conditional assembly: exact global containment and the coefficient
certificate's global generation identity imply equality of the actual
localized ideals. This is not a proof of either global hypothesis. -/
theorem localCritical_eq_localTarget_of_global_certificate
    (hcontainment : criticalIdeal ≤ targetIdeal)
    (hgeneration : targetIdeal = criticalIdeal ⊔
      MvPolynomial.idealOfVars (Fin 16) ℂ * targetIdeal) :
    localCritical = localTarget := by
  have hlocalgeneration := congrArg (Ideal.map (algebraMap P Local)) hgeneration
  rw [Ideal.map_sup, Ideal.map_mul] at hlocalgeneration
  change localTarget = localCritical ⊔
    Ideal.map (algebraMap P Local) (MvPolynomial.idealOfVars (Fin 16) ℂ) * localTarget
    at hlocalgeneration
  apply le_antisymm (Ideal.map_mono hcontainment)
  exact LocalGeometry.ideal_le_of_le_sup_mul_of_le_jacobson
    localTarget_fg map_idealOfVars_le_local_jacobson hlocalgeneration.le

end ConcreteLocalGeometry

#print axioms ConcreteLocalGeometry.targetIdeal_fg
#print axioms ConcreteLocalGeometry.localTarget_fg
#print axioms ConcreteLocalGeometry.idealOfVars_le_origin
#print axioms ConcreteLocalGeometry.map_idealOfVars_le_local_jacobson
#print axioms ConcreteLocalGeometry.localCritical_eq_localTarget_of_global_certificate
