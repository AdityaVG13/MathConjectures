import ParametricTranslation

/-!
# The actual translated denominator in the genuine origin localization

This file evaluates the translated denominator and proves it is inverted by the
existing Localization.AtPrime origin for s != -1/2. It does not construct or
assert an equivalence of ambient geometric charts.
-/

namespace ParametricLocalGeometry
open MvPolynomial ConcreteLocalGeometry

/-- Exact origin value of the actual translated denominator polynomial. -/
theorem translated_denominator_value (s : ℂ) :
    evalOrigin (translation s den) = 1 + 2 * s := by
  simp [translation, evalOrigin, den, da, dq, dd, t, x] <;> ring

/-- The chart denominator misses the actual origin maximal ideal in this range. -/
theorem translated_denominator_not_mem (s : ℂ) (hs : s ≠ -(1 / 2 : ℂ)) :
    translation s den ∉ origin := by
  intro h
  have hz : evalOrigin (translation s den) = 0 := RingHom.mem_ker.mp h
  rw [translated_denominator_value] at hz
  apply hs
  linear_combination (1 / 2 : ℂ) * hz

/-- Consequently that denominator is a unit in the actual origin localization. -/
theorem translated_denominator_unit (s : ℂ) (hs : s ≠ -(1 / 2 : ℂ)) :
    IsUnit (algebraMap P Local (translation s den)) := by
  exact IsLocalization.map_units Local
    (⟨translation s den, translated_denominator_not_mem s hs⟩ : origin.primeCompl)

end ParametricLocalGeometry

#print axioms ParametricLocalGeometry.translated_denominator_value
#print axioms ParametricLocalGeometry.translated_denominator_not_mem
#print axioms ParametricLocalGeometry.translated_denominator_unit
