import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/- All-orders factorization infrastructure. This does not assert that a formal
Morse coordinate change exists for the permanent; those premises are separate. -/
namespace ExceptionalFormal
open MvPowerSeries

noncomputable def shiftSeries {σ : Type*} (m : σ →₀ ℕ)
    (f : MvPowerSeries σ ℂ) : MvPowerSeries σ ℂ :=
  fun n => coeff (n + m) f

theorem monomial_factor_of_support {σ : Type*} (m : σ →₀ ℕ)
    (f : MvPowerSeries σ ℂ)
    (h : ∀ n, ¬m ≤ n → coeff n f = 0) :
    f = monomial m 1 * shiftSeries m f := by
  ext n
  rw [coeff_monomial_mul]
  split_ifs with hn
  · simp only [one_mul, shiftSeries, coeff_apply, tsub_add_cancel_of_le hn]
  · exact h n hn

theorem monomial_unit_of_support {σ : Type*} (m : σ →₀ ℕ)
    (f : MvPowerSeries σ ℂ)
    (h : ∀ n, ¬m ≤ n → coeff n f = 0)
    (hc : coeff m f ≠ 0) :
    ∃ u : MvPowerSeries σ ℂ, IsUnit u ∧ f = monomial m 1 * u := by
  refine ⟨shiftSeries m f, ?_, monomial_factor_of_support m f h⟩
  rw [isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  change coeff (0 + m) f ≠ 0
  simpa only [zero_add] using hc

#print axioms monomial_unit_of_support
end ExceptionalFormal
