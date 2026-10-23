import NinePivotEquivalence
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

private abbrev ExpectedOpen (R : Type u) [CommRing R] :=
  {M : Matrix (Fin 5) (Fin 5) R //
    ∀ k : Fin 9, IsUnit (M (expectedPivots k).1 (expectedPivots k).2)}
private abbrev ExpectedSlice (R : Type u) [CommRing R] :=
  {M : Matrix (Fin 5) (Fin 5) R //
    ∀ k : Fin 9, M (expectedPivots k).1 (expectedPivots k).2 = 1}

noncomputable def audit_expected_fiber_equiv (u : Fin 9 → Rˣ) :
    {M : Matrix (Fin 5) (Fin 5) R //
      ∀ k : Fin 9, M (expectedPivots k).1 (expectedPivots k).2 = (u k : R)} ≃
    ExpectedSlice R :=
  PermanentGauge.pivotFiberEquiv u

noncomputable def audit_expected_open_equiv :
    ExpectedOpen R ≃ (Fin 9 → Rˣ) × ExpectedSlice R :=
  PermanentGauge.pivotOpenEquiv

theorem audit_unit_selection (M : ExpectedOpen R) (k : Fin 9) :
    (audit_expected_open_equiv M).1 k = (M.property k).unit := rfl

theorem audit_forward_units_value (M : ExpectedOpen R) (k : Fin 9) :
    ((audit_expected_open_equiv M).1 k : R) =
      M.val (expectedPivots k).1 (expectedPivots k).2 :=
  PermanentGauge.pivotUnits_value M k

theorem audit_forward_matrix (M : ExpectedOpen R) :
    (audit_expected_open_equiv M).2.val =
      expectedNormalize ((audit_expected_open_equiv M).1) M.val := rfl

theorem audit_inverse_matrix (u : Fin 9 → Rˣ) (N : ExpectedSlice R) :
    (audit_expected_open_equiv.symm (u, N)).val = expectedReconstruct u N.val := rfl

theorem audit_left_inverse (M : ExpectedOpen R) :
    audit_expected_open_equiv.symm (audit_expected_open_equiv M) = M :=
  audit_expected_open_equiv.symm_apply_apply M

theorem audit_right_inverse (u : Fin 9 → Rˣ) (N : ExpectedSlice R) :
    audit_expected_open_equiv (audit_expected_open_equiv.symm (u, N)) = (u, N) :=
  audit_expected_open_equiv.apply_symm_apply (u, N)

theorem audit_recovered_unit_tuple (u : Fin 9 → Rˣ) (N : ExpectedSlice R) :
    (audit_expected_open_equiv (audit_expected_open_equiv.symm (u, N))).1 = u :=
  PermanentGauge.pivotUnits_reconstructOpen u N

#print axioms PermanentGauge.inverse_pivot_factor
#print axioms PermanentGauge.reconstruct_pivots
#print axioms PermanentGauge.pivotFiberEquiv
#print axioms PermanentGauge.pivotUnits
#print axioms PermanentGauge.pivotUnits_value
#print axioms PermanentGauge.reconstructOpen
#print axioms PermanentGauge.pivotUnits_reconstructOpen
#print axioms PermanentGauge.pivotOpenEquiv
#print axioms audit_expected_fiber_equiv
#print axioms audit_expected_open_equiv
#print axioms audit_unit_selection
#print axioms audit_forward_units_value
#print axioms audit_forward_matrix
#print axioms audit_inverse_matrix
#print axioms audit_left_inverse
#print axioms audit_right_inverse
#print axioms audit_recovered_unit_tuple
#check @PermanentGauge.pivotFiberEquiv
#check @PermanentGauge.pivotOpenEquiv
#check @PermanentGauge.pivotUnits_value
#check @PermanentGauge.pivotUnits_reconstructOpen
set_option pp.all true in
#check @PermanentGauge.pivotOpenEquiv
set_option pp.all true in
#check @audit_expected_open_equiv
set_option pp.all true in
#check @audit_unit_selection
run_cmd do
  for n in (← Lean.getEnv).allImportedModuleNames do
    Lean.logInfo m!"AUDIT_IMPORT {n}"
