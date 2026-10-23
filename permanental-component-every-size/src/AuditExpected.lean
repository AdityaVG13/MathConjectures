import ExceptionalFactor

open MvPowerSeries

/-- Reviewer-controlled statement with coordinate maps and monomial expanded. -/
theorem audit_expected_type
    (f : MvPowerSeries (Fin 4) ℂ)
    (ha : rescale (fun j : Fin 4 => if j = 1 then (-1 : ℂ) else 1) f = -f)
    (hd : rescale (fun j : Fin 4 => if j = 2 then (-1 : ℂ) else 1) f = -f)
    (hq : rescale (fun j : Fin 4 => if j = 3 then (-1 : ℂ) else 1) f = -f)
    (hzero : rescale (fun j : Fin 4 => if j = 0 then (0 : ℂ) else 1) f = 0)
    (hderiv : rescale (fun j : Fin 4 => if j = 0 then (0 : ℂ) else 1)
      (pderiv 0 f) = 0)
    (hlead : coeff (Finsupp.single 0 2 + Finsupp.single 1 1 +
      Finsupp.single 2 1 + Finsupp.single 3 1) f ≠ 0) :
    ∃ u : MvPowerSeries (Fin 4) ℂ, IsUnit u ∧
      f = monomial (Finsupp.single 0 2 + Finsupp.single 1 1 +
        Finsupp.single 2 1 + Finsupp.single 3 1) 1 * u :=
  ExceptionalFormal.exceptional_factor_is_unit f ha hd hq hzero hderiv hlead

theorem audit_coordinate_indices :
    ExceptionalFormal.exceptionalExponent 0 = 2 ∧
    ExceptionalFormal.exceptionalExponent 1 = 1 ∧
    ExceptionalFormal.exceptionalExponent 2 = 1 ∧
    ExceptionalFormal.exceptionalExponent 3 = 1 := by
  norm_num [ExceptionalFormal.exceptionalExponent]

theorem audit_monomial_identity :
    (monomial ExceptionalFormal.exceptionalExponent (1 : ℂ)) =
      (X 0 : MvPowerSeries (Fin 4) ℂ)^2 * X 1 * X 2 * X 3 := by
  rw [X_pow_eq]
  simp only [X_def, monomial_mul_monomial, one_mul,
    ExceptionalFormal.exceptionalExponent]

#print axioms ExceptionalFormal.monomial_factor_of_support
#print axioms ExceptionalFormal.monomial_unit_of_support
#print axioms ExceptionalFormal.coeff_rescale_at_zero
#print axioms ExceptionalFormal.anti_invariance_zero_exponent
#print axioms ExceptionalFormal.restriction_zero_exponent
#print axioms ExceptionalFormal.derivative_restriction_zero_exponent_one
#print axioms ExceptionalFormal.exceptional_factor_is_unit
#print axioms audit_expected_type
#print axioms audit_coordinate_indices
#print axioms audit_monomial_identity
#check @ExceptionalFormal.exceptional_factor_is_unit
set_option pp.all true in
#check @ExceptionalFormal.exceptional_factor_is_unit
set_option pp.all true in
#check @audit_expected_type

run_cmd do
  for n in (← Lean.getEnv).allImportedModuleNames do
    Lean.logInfo m!"AUDIT_IMPORT {n}"
