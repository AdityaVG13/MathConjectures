import NinePivotNormalization
open Matrix
universe u
variable {R : Type u} [CommRing R]

private def expectedPivots : Fin 9 → Fin 5 × Fin 5 :=
  ![(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,3),(3,4),(4,3)]
private def expectedRows (u : Fin 9 → Rˣ) : Fin 5 → Rˣ :=
  ![1, u 0 / u 4, u 0 / u 5, u 3 / u 6, u 3 / u 8]
private def expectedCols (u : Fin 9 → Rˣ) : Fin 5 → Rˣ :=
  ![(u 0)⁻¹, (u 1)⁻¹, (u 2)⁻¹, (u 3)⁻¹, u 6 / (u 3 * u 7)]
private def expectedNormalize (u : Fin 9 → Rˣ)
    (M : Matrix (Fin 5) (Fin 5) R) : Matrix (Fin 5) (Fin 5) R :=
  fun i j => (expectedRows u i : R) * (expectedCols u j : R) * M i j
private def expectedReconstruct (u : Fin 9 → Rˣ)
    (M : Matrix (Fin 5) (Fin 5) R) : Matrix (Fin 5) (Fin 5) R :=
  fun i j => (((expectedRows u i)⁻¹ : Rˣ) : R) *
    (((expectedCols u j)⁻¹ : Rˣ) : R) * M i j

theorem audit_pivot_list : PermanentGauge.pivot = expectedPivots := rfl

theorem audit_pivots_distinct : Function.Injective PermanentGauge.pivot := by
  decide

theorem audit_pivot_factor (u : Fin 9 → Rˣ) (k : Fin 9) :
    expectedRows u (expectedPivots k).1 *
    expectedCols u (expectedPivots k).2 * u k = 1 :=
  PermanentGauge.pivot_factor u k

theorem audit_normalize_pivots (u : Fin 9 → Rˣ)
    (M : Matrix (Fin 5) (Fin 5) R)
    (h : ∀ k, M (expectedPivots k).1 (expectedPivots k).2 = (u k : R))
    (k : Fin 9) :
    expectedNormalize u M (expectedPivots k).1 (expectedPivots k).2 = 1 :=
  PermanentGauge.normalize_pivots u M h k

theorem audit_reconstruct_normalize (u : Fin 9 → Rˣ)
    (M : Matrix (Fin 5) (Fin 5) R) :
    expectedReconstruct u (expectedNormalize u M) = M :=
  PermanentGauge.reconstruct_normalize u M

theorem audit_normalize_reconstruct (u : Fin 9 → Rˣ)
    (M : Matrix (Fin 5) (Fin 5) R) :
    expectedNormalize u (expectedReconstruct u M) = M :=
  PermanentGauge.normalize_reconstruct u M

theorem audit_normalize_cofactorIdeal (u : Fin 9 → Rˣ)
    (M : Matrix (Fin 5) (Fin 5) R) :
    Ideal.span (Set.range (fun ij : Fin 5 × Fin 5 =>
      Matrix.permanent (fun k l : Fin 4 =>
        expectedNormalize u M (ij.1.succAbove k) (ij.2.succAbove l)))) =
    Ideal.span (Set.range (fun ij : Fin 5 × Fin 5 =>
      Matrix.permanent (fun k l : Fin 4 =>
        M (ij.1.succAbove k) (ij.2.succAbove l)))) :=
  PermanentGauge.normalize_cofactorIdeal u M

#print axioms PermanentGauge.pivot_factor
#print axioms PermanentGauge.normalize_pivots
#print axioms PermanentGauge.reconstruct_normalize
#print axioms PermanentGauge.normalize_reconstruct
#print axioms PermanentGauge.normalize_cofactorIdeal
#print axioms audit_pivot_list
#print axioms audit_pivots_distinct
#print axioms audit_pivot_factor
#print axioms audit_normalize_pivots
#print axioms audit_reconstruct_normalize
#print axioms audit_normalize_reconstruct
#print axioms audit_normalize_cofactorIdeal
#check @PermanentGauge.pivot_factor
#check @PermanentGauge.normalize_pivots
#check @PermanentGauge.reconstruct_normalize
#check @PermanentGauge.normalize_reconstruct
#check @PermanentGauge.normalize_cofactorIdeal
set_option pp.all true in
#check @PermanentGauge.normalize_pivots
set_option pp.all true in
#check @audit_normalize_pivots
set_option pp.all true in
#check @audit_normalize_cofactorIdeal
run_cmd do
  for n in (← Lean.getEnv).allImportedModuleNames do
    Lean.logInfo m!"AUDIT_IMPORT {n}"
