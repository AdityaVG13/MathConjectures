import CofactorScaling
open Matrix
universe u v

variable {R : Type u} [CommRing R]

theorem audit_permanent_expected {n : Type v} [Fintype n] [DecidableEq n]
    (r c : n → R) (M : Matrix n n R) :
    Matrix.permanent (fun i j => r i * c j * M i j) =
      (∏ i, r i) * (∏ j, c j) * M.permanent :=
  PermanentGauge.permanent_scaleMatrix r c M

theorem audit_cofactor_expected (r c : Fin 5 → Rˣ)
    (M : Matrix (Fin 5) (Fin 5) R) (ij : Fin 5 × Fin 5) :
    Matrix.permanent (fun k l : Fin 4 => (r (ij.1.succAbove k) : R) *
      (c (ij.2.succAbove l) : R) *
      M (ij.1.succAbove k) (ij.2.succAbove l)) =
    (((∏ k : Fin 4, r (ij.1.succAbove k)) *
      (∏ l : Fin 4, c (ij.2.succAbove l)) : Rˣ) : R) *
      Matrix.permanent (fun k l : Fin 4 => M (ij.1.succAbove k) (ij.2.succAbove l)) :=
  PermanentGauge.cofactor_scaleMatrix r c M ij

theorem audit_ideal_expected (r c : Fin 5 → Rˣ)
    (M : Matrix (Fin 5) (Fin 5) R) :
    Ideal.span (Set.range (fun ij : Fin 5 × Fin 5 =>
      Matrix.permanent (fun k l : Fin 4 => (r (ij.1.succAbove k) : R) *
        (c (ij.2.succAbove l) : R) *
        M (ij.1.succAbove k) (ij.2.succAbove l)))) =
    Ideal.span (Set.range (fun ij : Fin 5 × Fin 5 =>
      Matrix.permanent (fun k l : Fin 4 => M (ij.1.succAbove k) (ij.2.succAbove l)))) :=
  PermanentGauge.cofactorIdeal_scaleMatrix r c M

theorem audit_twenty_five_indices : Fintype.card (Fin 5 × Fin 5) = 25 := by
  norm_num

theorem audit_deletion_range (i : Fin 5) :
    Set.range (i.succAbove : Fin 4 → Fin 5) = {i}ᶜ :=
  Fin.range_succAbove i

#print axioms PermanentGauge.permanent_scaleMatrix
#print axioms PermanentGauge.cofactor_scaleMatrix
#print axioms PermanentGauge.cofactorIdeal_scaleMatrix
#print axioms audit_permanent_expected
#print axioms audit_cofactor_expected
#print axioms audit_ideal_expected
#print axioms audit_twenty_five_indices
#print axioms audit_deletion_range
#check @PermanentGauge.permanent_scaleMatrix
#check @PermanentGauge.cofactor_scaleMatrix
#check @PermanentGauge.cofactorIdeal_scaleMatrix
set_option pp.all true in
#check @PermanentGauge.cofactorIdeal_scaleMatrix
set_option pp.all true in
#check @audit_ideal_expected
run_cmd do
  for n in (← Lean.getEnv).allImportedModuleNames do
    Lean.logInfo m!"AUDIT_IMPORT {n}"
