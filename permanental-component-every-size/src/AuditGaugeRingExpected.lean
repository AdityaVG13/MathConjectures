import GaugeRingEquivalence
open Matrix
namespace GaugeRingAudit

private def expectedPivots : Fin 9 → Fin 5 × Fin 5 :=
  ![(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,3),(3,4),(4,3)]
private abbrev ExpectedP := MvPolynomial (Fin 5 × Fin 5) ℂ
private noncomputable def expectedDelta : ExpectedP :=
  ∏ k : Fin 9, MvPolynomial.X (expectedPivots k)
private abbrev ExpectedA := Localization.Away expectedDelta
private noncomputable def expectedMatrix : Matrix (Fin 5) (Fin 5) PermanentGauge.Coordinates.A :=
  fun i j => algebraMap ExpectedP PermanentGauge.Coordinates.A (MvPolynomial.X (i,j))
private noncomputable def expectedRows (u : Fin 9 → PermanentGauge.Coordinates.Aˣ) : Fin 5 → PermanentGauge.Coordinates.Aˣ :=
  ![1, u 0 / u 4, u 0 / u 5, u 3 / u 6, u 3 / u 8]
private noncomputable def expectedCols (u : Fin 9 → PermanentGauge.Coordinates.Aˣ) : Fin 5 → PermanentGauge.Coordinates.Aˣ :=
  ![(u 0)⁻¹, (u 1)⁻¹, (u 2)⁻¹, (u 3)⁻¹, u 6 / (u 3 * u 7)]
private noncomputable def expectedClear : Matrix (Fin 5) (Fin 5) PermanentGauge.Coordinates.A := by
  classical
  exact fun i j => if ∃ k, expectedPivots k = (i,j) then 1 else expectedMatrix i j
private noncomputable def expectedForward (ij : Fin 5 × Fin 5) : PermanentGauge.Coordinates.A := by
  classical
  exact if ∃ k, expectedPivots k = ij then expectedMatrix ij.1 ij.2 else
    (expectedRows PermanentGauge.Coordinates.units ij.1 : PermanentGauge.Coordinates.A) *
    (expectedCols PermanentGauge.Coordinates.units ij.2 : PermanentGauge.Coordinates.A) *
    expectedMatrix ij.1 ij.2
private noncomputable def expectedInverse (ij : Fin 5 × Fin 5) : PermanentGauge.Coordinates.A :=
  (((expectedRows PermanentGauge.Coordinates.units ij.1)⁻¹ : PermanentGauge.Coordinates.Aˣ) : PermanentGauge.Coordinates.A) *
  (((expectedCols PermanentGauge.Coordinates.units ij.2)⁻¹ : PermanentGauge.Coordinates.Aˣ) : PermanentGauge.Coordinates.A) *
  expectedClear ij.1 ij.2

noncomputable def audit_expected_equiv : ExpectedA ≃+* ExpectedA :=
  PermanentGauge.Coordinates.coordinateRingEquiv

noncomputable def audit_operational_equiv :
    PermanentGauge.Coordinates.A ≃+* PermanentGauge.Coordinates.A :=
  PermanentGauge.Coordinates.coordinateRingEquiv

theorem audit_actual_ring_type : PermanentGauge.Coordinates.A = ExpectedA := rfl

theorem audit_delta_nonzero : expectedDelta ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k _
  exact MvPolynomial.X_ne_zero (expectedPivots k)

theorem audit_unit_values (k : Fin 9) :
    (PermanentGauge.Coordinates.units k : PermanentGauge.Coordinates.A) =
      expectedMatrix (expectedPivots k).1 (expectedPivots k).2 :=
  PermanentGauge.Coordinates.units_value k

theorem audit_clear_definition :
    expectedClear = PermanentGauge.Coordinates.clearPivots PermanentGauge.Coordinates.matrix := by
  ext i j
  classical
  by_cases h : PermanentGauge.Coordinates.IsPivot (i,j)
  · have h' : ∃ k, expectedPivots k = (i,j) := h
    simp [expectedClear, PermanentGauge.Coordinates.clearPivots, h, h']
  · have h' : ¬∃ k, expectedPivots k = (i,j) := h
    simp [expectedClear, PermanentGauge.Coordinates.clearPivots, h, h',
      expectedMatrix, PermanentGauge.Coordinates.matrix]

theorem audit_forward_generator (i j : Fin 5) :
    audit_operational_equiv (expectedMatrix i j) = expectedForward (i,j) :=
by
  change PermanentGauge.Coordinates.forwardMap (PermanentGauge.Coordinates.matrix i j) = _
  rw [PermanentGauge.Coordinates.forwardMap_matrix]
  classical
  by_cases h : PermanentGauge.Coordinates.IsPivot (i,j)
  · have h' : ∃ k, expectedPivots k = (i,j) := h
    simp [PermanentGauge.Coordinates.forwardImage, expectedForward, h, h',
      expectedMatrix, PermanentGauge.Coordinates.matrix]
  · have h' : ¬∃ k, expectedPivots k = (i,j) := h
    simp [PermanentGauge.Coordinates.forwardImage, expectedForward, h, h',
      PermanentGauge.normalize, PermanentGauge.scaleMatrix,
      expectedRows, expectedCols, PermanentGauge.rowFactor, PermanentGauge.colFactor,
      expectedMatrix, PermanentGauge.Coordinates.matrix]

theorem audit_inverse_generator (i j : Fin 5) :
    audit_operational_equiv.symm (expectedMatrix i j) = expectedInverse (i,j) :=
by
  change PermanentGauge.Coordinates.inverseMap (PermanentGauge.Coordinates.matrix i j) = _
  rw [PermanentGauge.Coordinates.inverseMap_matrix]
  unfold PermanentGauge.Coordinates.inverseImage expectedInverse
  rw [audit_clear_definition]
  rfl

theorem audit_forward_constant (a : ℂ) :
    audit_operational_equiv (algebraMap ExpectedP PermanentGauge.Coordinates.A (MvPolynomial.C a)) =
      algebraMap ExpectedP PermanentGauge.Coordinates.A (MvPolynomial.C a) :=
  PermanentGauge.Coordinates.forwardMap_constant a

theorem audit_inverse_constant (a : ℂ) :
    audit_operational_equiv.symm (algebraMap ExpectedP PermanentGauge.Coordinates.A (MvPolynomial.C a)) =
      algebraMap ExpectedP PermanentGauge.Coordinates.A (MvPolynomial.C a) :=
  PermanentGauge.Coordinates.inverseMap_constant a

theorem audit_left_inverse (x : PermanentGauge.Coordinates.A) :
    audit_operational_equiv.symm (audit_operational_equiv x) = x :=
  audit_operational_equiv.symm_apply_apply x

theorem audit_right_inverse (x : PermanentGauge.Coordinates.A) :
    audit_operational_equiv (audit_operational_equiv.symm x) = x :=
  audit_operational_equiv.apply_symm_apply x

theorem audit_forward_hom :
    audit_operational_equiv.toRingHom = PermanentGauge.Coordinates.forwardMap := rfl

theorem audit_inverse_hom :
    audit_operational_equiv.symm.toRingHom = PermanentGauge.Coordinates.inverseMap := by
  ext x
  rfl

private noncomputable def expectedCofactorIdeal
    (M : Matrix (Fin 5) (Fin 5) PermanentGauge.Coordinates.A) :=
    Ideal.span (Set.range (fun ij : Fin 5 × Fin 5 =>
      Matrix.permanent (fun k l : Fin 4 => M (ij.1.succAbove k) (ij.2.succAbove l))))

theorem audit_matrix_definition : expectedMatrix = PermanentGauge.Coordinates.matrix := rfl

theorem audit_cofactor_definition
    (M : Matrix (Fin 5) (Fin 5) PermanentGauge.Coordinates.A) :
    expectedCofactorIdeal M = PermanentGauge.cofactorIdeal M := rfl

theorem audit_ideal_orientation :
    Ideal.map audit_operational_equiv.symm.toRingHom
      (expectedCofactorIdeal expectedMatrix) = expectedCofactorIdeal expectedClear := by
  simp only [audit_inverse_hom, audit_cofactor_definition,
    audit_matrix_definition, audit_clear_definition]
  exact PermanentGauge.Coordinates.inverseMap_cofactorIdeal

end GaugeRingAudit

#print axioms PermanentGauge.Coordinates.delta
#print axioms PermanentGauge.Coordinates.matrix
#print axioms PermanentGauge.Coordinates.pivot_isUnit
#print axioms PermanentGauge.Coordinates.units
#print axioms PermanentGauge.Coordinates.units_value
#print axioms PermanentGauge.Coordinates.clearPivots
#print axioms PermanentGauge.Coordinates.clearPivots_at
#print axioms PermanentGauge.Coordinates.forwardImage
#print axioms PermanentGauge.Coordinates.inverseImage
#print axioms PermanentGauge.Coordinates.forwardImage_pivot
#print axioms PermanentGauge.Coordinates.inverseImage_pivot
#print axioms PermanentGauge.Coordinates.forwardPoly
#print axioms PermanentGauge.Coordinates.inversePoly
#print axioms PermanentGauge.Coordinates.forwardPoly_delta
#print axioms PermanentGauge.Coordinates.inversePoly_delta
#print axioms PermanentGauge.Coordinates.forwardMap
#print axioms PermanentGauge.Coordinates.inverseMap
#print axioms PermanentGauge.Coordinates.forwardMap_matrix
#print axioms PermanentGauge.Coordinates.inverseMap_matrix
#print axioms PermanentGauge.Coordinates.inverseImage_cofactorIdeal
#print axioms PermanentGauge.Coordinates.forwardMap_units
#print axioms PermanentGauge.Coordinates.inverseMap_units
#print axioms PermanentGauge.Coordinates.map_rowFactor
#print axioms PermanentGauge.Coordinates.map_colFactor
#print axioms PermanentGauge.Coordinates.map_normalize
#print axioms PermanentGauge.Coordinates.map_reconstruct
#print axioms PermanentGauge.Coordinates.map_clearPivots
#print axioms PermanentGauge.Coordinates.inverse_forward_matrix
#print axioms PermanentGauge.Coordinates.forward_clear_matrix
#print axioms PermanentGauge.Coordinates.forward_inverse_matrix
#print axioms PermanentGauge.Coordinates.forwardMap_constant
#print axioms PermanentGauge.Coordinates.inverseMap_constant
#print axioms PermanentGauge.Coordinates.inverse_comp_forward
#print axioms PermanentGauge.Coordinates.forward_comp_inverse
#print axioms PermanentGauge.Coordinates.coordinateRingEquiv
#print axioms PermanentGauge.Coordinates.inverseMap_cofactorIdeal
#print axioms GaugeRingAudit.audit_expected_equiv
#print axioms GaugeRingAudit.audit_operational_equiv
#print axioms GaugeRingAudit.audit_actual_ring_type
#print axioms GaugeRingAudit.audit_delta_nonzero
#print axioms GaugeRingAudit.audit_unit_values
#print axioms GaugeRingAudit.audit_forward_generator
#print axioms GaugeRingAudit.audit_inverse_generator
#print axioms GaugeRingAudit.audit_forward_constant
#print axioms GaugeRingAudit.audit_inverse_constant
#print axioms GaugeRingAudit.audit_left_inverse
#print axioms GaugeRingAudit.audit_right_inverse
#print axioms GaugeRingAudit.audit_forward_hom
#print axioms GaugeRingAudit.audit_inverse_hom
#print axioms GaugeRingAudit.audit_matrix_definition
#print axioms GaugeRingAudit.audit_clear_definition
#print axioms GaugeRingAudit.audit_cofactor_definition
#print axioms GaugeRingAudit.audit_ideal_orientation
#check @PermanentGauge.Coordinates.coordinateRingEquiv
#check @PermanentGauge.Coordinates.inverse_comp_forward
#check @PermanentGauge.Coordinates.forward_comp_inverse
#check @PermanentGauge.Coordinates.inverseMap_cofactorIdeal
set_option pp.all true in
#check @GaugeRingAudit.audit_expected_equiv
set_option pp.all true in
#check @GaugeRingAudit.audit_ideal_orientation
#print Localization.Away
run_cmd do
  for n in (← Lean.getEnv).allImportedModuleNames do
    Lean.logInfo m!"AUDIT_IMPORT {n}"
