import SymmetrySupport
namespace ExceptionalFormal
open MvPowerSeries

/-- Exponents of t² a d q. Coordinates are ordered t,a,d,q. -/
noncomputable def exceptionalExponent : Fin 4 →₀ ℕ :=
  Finsupp.single 0 2 + Finsupp.single 1 1 + Finsupp.single 2 1 + Finsupp.single 3 1

theorem derivative_restriction_zero_exponent_one
    (f : MvPowerSeries (Fin 4) ℂ)
    (h : rescale (scaleAt 0 0) (pderiv 0 f) = 0)
    (n : Fin 4 →₀ ℕ) (hn : n 0 = 1) : coeff n f = 0 := by
  let k := n - Finsupp.single 0 1
  have hk : k 0 = 0 := by simp [k, hn]
  have hle : Finsupp.single 0 1 ≤ n := by
    intro i
    by_cases hi : i = 0
    · subst i; simp [hn]
    · simp [Finsupp.single_apply, hi]
  have he := restriction_zero_exponent (pderiv 0 f) 0 h k hk
  rw [coeff_pderiv, hk] at he
  have hs : k + Finsupp.single 0 1 = n := tsub_add_cancel_of_le hle
  simpa only [hs, Nat.cast_zero, zero_add, mul_one] using he

/-- A conditional, all-orders theorem. The hypotheses refer to genuine power
series rescaling and differentiation. No coordinate change is postulated as a
proved fact about the permanent here. -/
theorem exceptional_factor_is_unit
    (f : MvPowerSeries (Fin 4) ℂ)
    (ha : rescale (scaleAt 1 (-1)) f = -f)
    (hd : rescale (scaleAt 2 (-1)) f = -f)
    (hq : rescale (scaleAt 3 (-1)) f = -f)
    (hzero : rescale (scaleAt 0 0) f = 0)
    (hderiv : rescale (scaleAt 0 0) (pderiv 0 f) = 0)
    (hlead : coeff exceptionalExponent f ≠ 0) :
    ∃ u : MvPowerSeries (Fin 4) ℂ,
      IsUnit u ∧ f = monomial exceptionalExponent 1 * u := by
  apply monomial_unit_of_support exceptionalExponent f ?_ hlead
  intro n hn
  by_cases h0 : 2 ≤ n 0
  · by_cases h1 : 1 ≤ n 1
    · by_cases h2 : 1 ≤ n 2
      · by_cases h3 : 1 ≤ n 3
        · exfalso
          apply hn
          intro i
          fin_cases i
          · simpa [exceptionalExponent] using h0
          · simpa [exceptionalExponent] using h1
          · simpa [exceptionalExponent] using h2
          · simpa [exceptionalExponent] using h3
        · apply anti_invariance_zero_exponent f 3 hq n
          omega
      · apply anti_invariance_zero_exponent f 2 hd n
        omega
    · apply anti_invariance_zero_exponent f 1 ha n
      omega
  · have hz : n 0 = 0 ∨ n 0 = 1 := by omega
    rcases hz with hz | hz
    · exact restriction_zero_exponent f 0 hzero n hz
    · exact derivative_restriction_zero_exponent_one f hderiv n hz

#print axioms exceptional_factor_is_unit
end ExceptionalFormal
