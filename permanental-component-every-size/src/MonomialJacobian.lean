import ExceptionalFactor
import Mathlib.RingTheory.Ideal.Span

namespace ExceptionalFormal
open MvPowerSeries
abbrev Series := MvPowerSeries (Fin 4) ℂ

noncomputable def exceptionalMonomial : Series := X 0 ^ 2 * X 1 * X 2 * X 3
noncomputable def residualGenerator : Fin 4 → Series :=
  ![X 0 * X 1 * X 2 * X 3, X 0 ^ 2 * X 2 * X 3,
    X 0 ^ 2 * X 1 * X 3, X 0 ^ 2 * X 1 * X 2]
noncomputable def derivativeUnit (u : Series) (i : Fin 4) : Series :=
  (if i = 0 then 2 else 1) * u + X i * pderiv i u
noncomputable def jacobianIdeal (f : Series) : Ideal Series :=
  Ideal.span (Set.range (fun i : Fin 4 => pderiv i f))
noncomputable def residualIdeal : Ideal Series :=
  Ideal.span (Set.range residualGenerator)

theorem exceptionalMonomial_eq : exceptionalMonomial = monomial exceptionalExponent 1 := by
  unfold exceptionalMonomial
  rw [X_pow_eq]
  simp only [exceptionalExponent, X_def, monomial_mul_monomial, one_mul]

theorem monomial_unit_derivative (u : Series) (i : Fin 4) :
    pderiv i (exceptionalMonomial * u) = residualGenerator i * derivativeUnit u i := by
  fin_cases i <;>
    simp [exceptionalMonomial, residualGenerator, derivativeUnit,
      Derivation.leibniz, pderiv_pow, pderiv_X_of_ne] <;> ring

theorem derivativeUnit_isUnit (u : Series) (hu : IsUnit u) (i : Fin 4) :
    IsUnit (derivativeUnit u i) := by
  rw [isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  have hc : constantCoeff u ≠ 0 :=
    isUnit_iff_ne_zero.mp (isUnit_iff_constantCoeff.mp hu)
  have hc2 : constantCoeff (2 : Series) = (2 : ℂ) := by
    rw [show (2 : Series) = 1 + 1 by ring]
    rw [map_add, map_one]
    norm_num
  fin_cases i <;> simp [derivativeUnit, hc, hc2]

/-- Multiplication by a unit preserves this monomial's Jacobian ideal.
This theorem makes no such assertion for an arbitrary power series. -/
theorem monomial_unit_jacobian (u : Series) (hu : IsUnit u) :
    jacobianIdeal (exceptionalMonomial * u) = residualIdeal := by
  simp only [jacobianIdeal, residualIdeal, Ideal.span_range_eq_iSup]
  apply iSup_congr
  intro i
  rw [monomial_unit_derivative]
  exact Ideal.span_singleton_mul_right_unit (derivativeUnit_isUnit u hu i) _

theorem symmetry_jacobian_eq_residual
    (f : Series)
    (ha : rescale (scaleAt 1 (-1)) f = -f)
    (hd : rescale (scaleAt 2 (-1)) f = -f)
    (hq : rescale (scaleAt 3 (-1)) f = -f)
    (hzero : rescale (scaleAt 0 0) f = 0)
    (hderiv : rescale (scaleAt 0 0) (pderiv 0 f) = 0)
    (hlead : coeff exceptionalExponent f ≠ 0) :
    jacobianIdeal f = residualIdeal := by
  obtain ⟨u, hu, hf⟩ := exceptional_factor_is_unit f ha hd hq hzero hderiv hlead
  rw [← exceptionalMonomial_eq] at hf
  rw [hf]
  exact monomial_unit_jacobian u hu

#print axioms monomial_unit_jacobian
#print axioms symmetry_jacobian_eq_residual
end ExceptionalFormal
