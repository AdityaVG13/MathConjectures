import ResidualNonreduced
open MvPowerSeries

theorem audit_nil_witness_not_mem :
    (X 0 * X 1 * X 2 : MvPowerSeries (Fin 4) ℂ) ∉
    Ideal.span (Set.range (fun i : Fin 4 =>
      (![X 0 * X 1 * X 2 * X 3, X 0 ^ 2 * X 2 * X 3,
         X 0 ^ 2 * X 1 * X 3, X 0 ^ 2 * X 1 * X 2] :
         Fin 4 → MvPowerSeries (Fin 4) ℂ) i)) :=
  ExceptionalFormal.nilWitness_not_mem

theorem audit_nil_witness_square_mem :
    (X 0 * X 1 * X 2 : MvPowerSeries (Fin 4) ℂ)^2 ∈
    Ideal.span (Set.range (fun i : Fin 4 =>
      (![X 0 * X 1 * X 2 * X 3, X 0 ^ 2 * X 2 * X 3,
         X 0 ^ 2 * X 1 * X 3, X 0 ^ 2 * X 1 * X 2] :
         Fin 4 → MvPowerSeries (Fin 4) ℂ) i)) :=
  ExceptionalFormal.nilWitness_sq_mem

theorem audit_nonradical_expected :
    ¬ (Ideal.span (Set.range (fun i : Fin 4 =>
      (![X 0 * X 1 * X 2 * X 3, X 0 ^ 2 * X 2 * X 3,
         X 0 ^ 2 * X 1 * X 3, X 0 ^ 2 * X 1 * X 2] :
         Fin 4 → MvPowerSeries (Fin 4) ℂ) i))).IsRadical :=
  ExceptionalFormal.residualIdeal_not_radical

theorem audit_nonreduced_expected :
    ¬ IsReduced ((MvPowerSeries (Fin 4) ℂ) ⧸
      Ideal.span (Set.range (fun i : Fin 4 =>
        (![X 0 * X 1 * X 2 * X 3, X 0 ^ 2 * X 2 * X 3,
           X 0 ^ 2 * X 1 * X 3, X 0 ^ 2 * X 1 * X 2] :
           Fin 4 → MvPowerSeries (Fin 4) ℂ) i))) :=
  ExceptionalFormal.residualQuotient_not_reduced

#print axioms ExceptionalFormal.downsetZero
#print axioms ExceptionalFormal.residualGenerator_monomial
#print axioms ExceptionalFormal.residual_not_le_nil
#print axioms ExceptionalFormal.residualIdeal_le_downset
#print axioms ExceptionalFormal.nilWitness_not_mem
#print axioms ExceptionalFormal.nilWitness_sq_mem
#print axioms ExceptionalFormal.residualIdeal_not_radical
#print axioms ExceptionalFormal.residualQuotient_not_reduced
#print axioms audit_nil_witness_not_mem
#print axioms audit_nil_witness_square_mem
#print axioms audit_nonradical_expected
#print axioms audit_nonreduced_expected
#check @ExceptionalFormal.residualIdeal_not_radical
#check @ExceptionalFormal.residualQuotient_not_reduced
set_option pp.all true in
#check @audit_nonradical_expected
set_option pp.all true in
#check @audit_nonreduced_expected
run_cmd do
  for n in (← Lean.getEnv).allImportedModuleNames do
    Lean.logInfo m!"AUDIT_IMPORT {n}"
