import GeometryBridge.UpperQuadraticChart
import GeometryBridge.NormalizedUpperEquiv
import DimensionClosure.FiniteTypeDimension
import Mathlib.RingTheory.Etale.StandardEtale

namespace UniformUpperQuadratic
noncomputable section
open Polynomial

theorem base_dimension : ringKrullDim Base = 2 := by
  have hi : Function.Injective (algebraMap Parameters Base) :=
    IsLocalization.injective Base (powers_le_nonZeroDivisors_of_noZeroDivisors denom_ne_zero)
  rw [ComponentDimensionClosure.localization_dimension ℂ Parameters Base
    (Submonoid.powers (denom d h)) hi]
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp

theorem component_dimension_two (Q : Ideal Chart) (hQ : IsMinimalPrime Q) :
    ringKrullDim (Chart ⧸ Q) = 2 := by
  rw [component_dimension Q hQ, base_dimension]

theorem base_discriminant_unit : IsUnit (algebraMap Parameters Base (disc d h)) := by
  apply IsLocalization.Away.isUnit_of_dvd (x := denom d h)
  use alpha d h * normPlus d h * normMinus d h
  simp only [denom, rest]
  ring

theorem normalized_discriminant_identity :
    algebraMap Parameters Base (alpha d h)^2 * (b^2-4*c) =
      algebraMap Parameters Base (disc d h) := by
  calc
    _ = (algebraMap Parameters Base (alpha d h)*b)^2 -
      4*algebraMap Parameters Base (alpha d h)*(algebraMap Parameters Base (alpha d h)*c) := by ring
    _ = _ := by rw [alpha_mul_b, alpha_mul_c]; simp [disc, map_ofNat]

theorem normalized_discriminant_unit : IsUnit (b^2-4*c) :=
  isUnit_of_mul_isUnit_right (normalized_discriminant_identity.symm ▸ base_discriminant_unit)

theorem derivative_value_unit : IsUnit (2*j + algebraMap Base Chart b) := by
  have hs : (2*j + algebraMap Base Chart b)*(2*j + algebraMap Base Chart b) =
      algebraMap Base Chart (b^2-4*c) := by
    simp only [map_sub, map_pow, map_mul, map_ofNat]
    linear_combination 4 * root_equation
  apply isUnit_of_mul_isUnit_left (y := 2*j + algebraMap Base Chart b)
  rw [hs]
  exact normalized_discriminant_unit.map (algebraMap Base Chart)

theorem derivative_unit : IsUnit (AdjoinRoot.mk equation equation.derivative) := by
  have he : AdjoinRoot.mk equation equation.derivative = 2*j + algebraMap Base Chart b := by
    have hd : equation.derivative = C 2 * X + C b := by
      simp [equation, map_ofNat]
      ring
    rw [hd, map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
    change algebraMap Base Chart 2 * j + algebraMap Base Chart b = _
    rw [map_ofNat]
  rw [he]
  exact derivative_value_unit

/-- A monic root algebra with invertible derivative is smooth, via the actual
standard etale presentation localized at that derivative. -/
theorem smooth_adjoinRoot_of_derivative_unit {R : Type*} [CommRing R]
    (f : R[X]) (hf : f.Monic) (hu : IsUnit (AdjoinRoot.mk f f.derivative)) :
    Algebra.Smooth R (AdjoinRoot f) := by
  let P : StandardEtalePair R := ⟨f, hf, f.derivative, ⟨1, 0, 1, by simp⟩⟩
  let e : P.Ring ≃ₐ[R] AdjoinRoot f :=
    P.equivAwayAdjoinRoot.trans
      ((IsLocalization.atUnit (AdjoinRoot f) (Localization.Away (AdjoinRoot.mk f f.derivative))
        (AdjoinRoot.mk f f.derivative) hu).symm.restrictScalars R)
  exact Algebra.Smooth.of_equiv e

instance chart_smooth_base : Algebra.Smooth Base Chart :=
  smooth_adjoinRoot_of_derivative_unit equation equation_monic derivative_unit

instance base_smooth : Algebra.Smooth ℂ Base := by
  letI : Algebra.Smooth ℂ Parameters := ⟨inferInstance, inferInstance⟩
  letI : Algebra.Smooth Parameters Base := Algebra.Smooth.of_isLocalization_Away (denom d h)
  exact Algebra.Smooth.comp ℂ Parameters Base

instance chart_smooth : Algebra.Smooth ℂ Chart := Algebra.Smooth.comp ℂ Base Chart

#print axioms base_dimension
#print axioms component_dimension_two
#print axioms derivative_unit
#print axioms chart_smooth
end
end UniformUpperQuadratic

namespace UniformNormalizedUpper
noncomputable section
/-- Smoothness of the actual localized four-permanent normalized upper chart. -/
instance normalized_smooth : Algebra.Smooth ℂ Normalized :=
  Algebra.Smooth.of_equiv normalizedAlgEquiv
#print axioms normalized_smooth
end
end UniformNormalizedUpper
