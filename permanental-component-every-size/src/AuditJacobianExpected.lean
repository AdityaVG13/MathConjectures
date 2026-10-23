import MonomialJacobian
open MvPowerSeries

theorem audit_jacobian_unit_type
    (u : MvPowerSeries (Fin 4) ℂ) (hu : IsUnit u) :
    Ideal.span (Set.range (fun i : Fin 4 =>
      pderiv i ((X 0 ^ 2 * X 1 * X 2 * X 3) * u))) =
    Ideal.span (Set.range (fun i : Fin 4 =>
      (![X 0 * X 1 * X 2 * X 3, X 0 ^ 2 * X 2 * X 3,
         X 0 ^ 2 * X 1 * X 3, X 0 ^ 2 * X 1 * X 2] :
         Fin 4 → MvPowerSeries (Fin 4) ℂ) i)) :=
  ExceptionalFormal.monomial_unit_jacobian u hu

theorem audit_residual_generator_order :
    ExceptionalFormal.residualGenerator 0 = X 0 * X 1 * X 2 * X 3 ∧
    ExceptionalFormal.residualGenerator 1 = X 0 ^ 2 * X 2 * X 3 ∧
    ExceptionalFormal.residualGenerator 2 = X 0 ^ 2 * X 1 * X 3 ∧
    ExceptionalFormal.residualGenerator 3 = X 0 ^ 2 * X 1 * X 2 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem audit_combined_jacobian_type
    (f : MvPowerSeries (Fin 4) ℂ)
    (ha : rescale (fun j : Fin 4 => if j = 1 then (-1 : ℂ) else 1) f = -f)
    (hd : rescale (fun j : Fin 4 => if j = 2 then (-1 : ℂ) else 1) f = -f)
    (hq : rescale (fun j : Fin 4 => if j = 3 then (-1 : ℂ) else 1) f = -f)
    (hzero : rescale (fun j : Fin 4 => if j = 0 then (0 : ℂ) else 1) f = 0)
    (hderiv : rescale (fun j : Fin 4 => if j = 0 then (0 : ℂ) else 1)
      (pderiv 0 f) = 0)
    (hlead : coeff (Finsupp.single 0 2 + Finsupp.single 1 1 +
      Finsupp.single 2 1 + Finsupp.single 3 1) f ≠ 0) :
    Ideal.span (Set.range (fun i : Fin 4 => pderiv i f)) =
    Ideal.span (Set.range (fun i : Fin 4 =>
      (![X 0 * X 1 * X 2 * X 3, X 0 ^ 2 * X 2 * X 3,
         X 0 ^ 2 * X 1 * X 3, X 0 ^ 2 * X 1 * X 2] :
         Fin 4 → MvPowerSeries (Fin 4) ℂ) i)) :=
  ExceptionalFormal.symmetry_jacobian_eq_residual f ha hd hq hzero hderiv hlead

#print axioms ExceptionalFormal.exceptionalMonomial_eq
#print axioms ExceptionalFormal.monomial_unit_derivative
#print axioms ExceptionalFormal.derivativeUnit_isUnit
#print axioms ExceptionalFormal.monomial_unit_jacobian
#print axioms ExceptionalFormal.symmetry_jacobian_eq_residual
#print axioms audit_jacobian_unit_type
#print axioms audit_residual_generator_order
#print axioms audit_combined_jacobian_type
#check @ExceptionalFormal.monomial_unit_jacobian
#check @ExceptionalFormal.symmetry_jacobian_eq_residual
set_option pp.all true in
#check @ExceptionalFormal.symmetry_jacobian_eq_residual
set_option pp.all true in
#check @audit_combined_jacobian_type
run_cmd do
  for n in (← Lean.getEnv).allImportedModuleNames do
    Lean.logInfo m!"AUDIT_IMPORT {n}"
