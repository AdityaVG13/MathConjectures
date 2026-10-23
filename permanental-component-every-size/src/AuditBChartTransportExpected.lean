import BChartAmbientTransport

namespace BChartTransportAudit
open Matrix MvPolynomial
open PermanentGauge.Coordinates

private noncomputable def expectedAssignment (s : ℂ) : Fin 16 → P :=
  ![X (4,0)-C s,X (0,4),X (1,3),X (3,1),X (1,1),X (1,2)+1,X (1,4),X (2,2)-1,
    X (2,3)-1,X (2,4),X (3,0)-C s,X (2,1)+1,X (3,2)-C s,X (4,1),X (4,2)-C s,X (4,4)+1]

private noncomputable def expectedDenominator : P :=
  (X (4,0)*(1-X (3,1)))*(1-(X (4,0)+1)*X (0,4))*(1+X (4,0)*X (1,3))

private noncomputable def expectedCofactorIdeal {R : Type*} [CommRing R]
    (M : Matrix (Fin 5) (Fin 5) R) : Ideal R :=
  Ideal.span (Set.range (fun ij : Fin 5 × Fin 5 =>
    Matrix.permanent (fun k l : Fin 4 => M (ij.1.succAbove k) (ij.2.succAbove l))))

private noncomputable def expectedTargetGenerators (s : ℂ) : Fin 15 → P :=
  ![X (1,1),X (1,2)+1,X (1,4),X (2,2)-1,X (2,3)-1,X (2,4),
    X (3,0)-C s,X (2,1)+1,X (3,2)-C s,X (4,1),X (4,2)-C s,X (4,4)+1,
    X (0,4)*X (1,3),X (0,4)*X (3,1),X (1,3)*X (3,1)]

private noncomputable def expectedUniversal : Matrix (Fin 5) (Fin 5) A :=
  fun i j => algebraMap P A (X (i,j))

noncomputable def audit_local_chart_hom (s : ℂ) :
    Localization.AtPrime ConcreteLocalGeometry.origin →+*
      Localization.AtPrime (pointIdeal s) := BChartTransport.localChartMap s

noncomputable def audit_translation_equiv (s : ℂ) (hs : s ≠ 0) (n : ℤ) :
    Localization.AtPrime (pointIdeal s) ≃+* Localization.AtPrime (pointIdeal s) :=
  BChartTransport.translationEquiv s hs n

noncomputable def audit_ambient_equiv (s : ℂ) (hs : s ≠ 0) :
    Localization.AtPrime (pointIdeal s) ≃+* Localization.AtPrime (pointIdeal s) :=
  BChartTransport.ambientChartEquiv s hs

theorem audit_assignment (s : ℂ) :
    BChartTransport.assignment s = expectedAssignment s := rfl

theorem audit_chart_substitution (s : ℂ) :
    BChartTransport.chartMap s = eval₂Hom C (expectedAssignment s) := rfl

theorem audit_denominator : BChartTransport.denominator = expectedDenominator := rfl

theorem audit_actual_matrix_correspondence (s : ℂ) :
    (fun i j => eval₂Hom C (expectedAssignment s) (BChartLocalGeometry.matrixAt s i j)) =
      BChartTransport.clearedMatrix s := BChartTransport.matrix_correspondence s

theorem audit_cofactor_definition {R : Type*} [CommRing R]
    (M : Matrix (Fin 5) (Fin 5) R) :
    expectedCofactorIdeal M = PermanentGauge.cofactorIdeal M := rfl

theorem audit_all25_correspondence (s : ℂ) :
    Ideal.map (eval₂Hom C (expectedAssignment s))
      (expectedCofactorIdeal (BChartLocalGeometry.matrixAt s)) =
      expectedCofactorIdeal (BChartTransport.clearedMatrix s) :=
  BChartTransport.ideal_correspondence s

theorem audit_local_hom_on_polynomials (s : ℂ) (f : ConcreteLocalGeometry.P) :
    audit_local_chart_hom s (algebraMap ConcreteLocalGeometry.P ConcreteLocalGeometry.Local f) =
      BChartTransport.toFamilyLocal s (eval₂Hom C (expectedAssignment s) f) :=
  RingHom.congr_fun (BChartTransport.localChartMap_source s) f

theorem audit_denominator_residue (s : ℂ) : pointPoly s expectedDenominator = s :=
  BChartTransport.denominator_value s

theorem audit_denominator_isunit (s : ℂ) (hs : s ≠ 0) :
    IsUnit (BChartTransport.toFamilyLocal s expectedDenominator) :=
  BChartTransport.denominator_local_unit s hs

theorem audit_residue (s : ℂ) (f : P) :
    BChartTransport.residue s (BChartTransport.toFamilyLocal s f) = pointPoly s f :=
  BChartTransport.residue_polynomial s f

theorem audit_extend_at_point (s : ℂ) (g : A →+* LocalAt s)
    (hg : (BChartTransport.residue s).comp g = pointMap s) (x : A) :
    BChartTransport.extendAtPoint s g hg (algebraMap A (LocalAt s) x) = g x :=
  BChartTransport.extendAtPoint_toMap s g hg x

theorem audit_fraction_definitions (s : ℂ) (hs : s ≠ 0) :
    BChartTransport.jValue s hs =
      BChartTransport.toFamilyLocal s
        (X (4,0)*(1+X (0,4))*(X (4,0)*(1-X (3,1)))*(1+X (4,0)*X (1,3))) *
      (((BChartTransport.denominatorUnit s hs)⁻¹ : (LocalAt s)ˣ) : LocalAt s) ∧
    BChartTransport.zValue s hs =
      BChartTransport.toFamilyLocal s
        (X (4,0)*(1+X (1,3))*(X (4,0)*(1-X (3,1)))*(1-(X (4,0)+1)*X (0,4))) *
      (((BChartTransport.denominatorUnit s hs)⁻¹ : (LocalAt s)ˣ) : LocalAt s) ∧
    BChartTransport.qValue s hs =
      BChartTransport.toFamilyLocal s
        (-X (3,1)*(1+2*X (4,0))*(1-(X (4,0)+1)*X (0,4))*(1+X (4,0)*X (1,3))) *
      (((BChartTransport.denominatorUnit s hs)⁻¹ : (LocalAt s)ˣ) : LocalAt s) :=
  ⟨rfl,rfl,rfl⟩

theorem audit_eight_shifts (s : ℂ) (hs : s ≠ 0) :
    BChartTransport.shift s hs =
      !![0,0,0,0,0;
         0,0,-BChartTransport.raw s 1 3,0,0;
         0,BChartTransport.qValue s hs,0,-BChartTransport.qValue s hs,BChartTransport.raw s 0 4;
         BChartTransport.jValue s hs-BChartTransport.scalar s s,0,
         BChartTransport.jValue s hs+BChartTransport.zValue s hs-BChartTransport.raw s 4 0-BChartTransport.scalar s s,0,0;
         0,BChartTransport.raw s 3 1,BChartTransport.zValue s hs-BChartTransport.scalar s s,0,0] := rfl

theorem audit_actual_translation (s : ℂ) (hs : s ≠ 0) (n : ℤ) (i j : Fin 5) :
    audit_translation_equiv s hs n (BChartTransport.toFamilyLocal s (X (i,j))) =
      BChartTransport.toFamilyLocal s (X (i,j)) + (n : LocalAt s)*BChartTransport.shift s hs i j :=
  BChartTransport.translationMap_raw s hs n i j

theorem audit_translation_inverse_function (s : ℂ) (hs : s ≠ 0) (n : ℤ) (x : LocalAt s) :
    (audit_translation_equiv s hs n).symm x = BChartTransport.translationMap s hs (-n) x := rfl

theorem audit_translation_left_inverse (s : ℂ) (hs : s ≠ 0) (n : ℤ) (x : LocalAt s) :
    BChartTransport.translationMap s hs (-n) (BChartTransport.translationMap s hs n x) = x :=
  (audit_translation_equiv s hs n).symm_apply_apply x

theorem audit_translation_right_inverse (s : ℂ) (hs : s ≠ 0) (n : ℤ) (x : LocalAt s) :
    BChartTransport.translationMap s hs n (BChartTransport.translationMap s hs (-n) x) = x :=
  (audit_translation_equiv s hs n).apply_symm_apply x

theorem audit_translation_group_law (s : ℂ) (hs : s ≠ 0) (m n : ℤ) :
    (BChartTransport.translationMap s hs m).comp (BChartTransport.translationMap s hs n) =
      BChartTransport.translationMap s hs (m+n) := BChartTransport.translationMap_add s hs m n

theorem audit_actual_row_units (s : ℂ) (hs : s ≠ 0) :
    (fun i => (BChartTransport.rowClearing s hs i : LocalAt s)) =
      ![1,1,BChartTransport.toFamilyLocal s expectedDenominator,
        BChartTransport.toFamilyLocal s expectedDenominator,
        BChartTransport.toFamilyLocal s expectedDenominator] := by
  funext i
  fin_cases i <;> simp [BChartTransport.rowClearing, BChartTransport.denominatorUnit_value, audit_denominator]

theorem audit_actual_row_identity (s : ℂ) (hs : s ≠ 0) (i j : Fin 5) :
    (BChartTransport.rowClearing s hs i : LocalAt s) *
      BChartTransport.translationMap s hs 1
        (algebraMap A (LocalAt s) (clearPivots expectedUniversal i j)) =
      BChartTransport.toFamilyLocal s (BChartTransport.clearedMatrix s i j) := by
  have hU : expectedUniversal = PermanentGauge.Coordinates.matrix := rfl
  rw [hU]
  have h := congrFun (congrFun (BChartTransport.row_clearing_identity s hs) i) j
  simpa [PermanentGauge.scaleMatrix, BChartTransport.translatedNormalizedMatrix,
    BChartTransport.localNormalizedMatrix] using h

theorem audit_target_generator_images (s : ℂ) :
    BChartTransport.chartMap s ∘ ConcreteLocalGeometry.targetGenerator = expectedTargetGenerators s := by
  funext k
  fin_cases k <;> simp [BChartTransport.chartMap, BChartTransport.assignment,
    ConcreteLocalGeometry.targetGenerator, ConcreteLocalGeometry.x,
    BChartTransport.v, expectedTargetGenerators]

theorem audit_explicit_target (s : ℂ) :
    BChartTransport.localExpectedIdeal s =
      Ideal.map (BChartTransport.toFamilyLocal s) (Ideal.span (Set.range (expectedTargetGenerators s))) := by
  unfold BChartTransport.localExpectedIdeal ConcreteLocalGeometry.targetIdeal
  rw [Ideal.map_span, ← Set.range_comp, audit_target_generator_images]

theorem audit_basechanged_equality (s : ℂ) (hs : s ≠ 0) :
    Ideal.map (BChartTransport.toFamilyLocal s) (expectedCofactorIdeal (BChartTransport.clearedMatrix s)) =
      Ideal.map (BChartTransport.toFamilyLocal s) (Ideal.span (Set.range (expectedTargetGenerators s))) := by
  change BChartTransport.localClearedIdeal s = _
  rw [BChartTransport.localCleared_eq_expected s hs, audit_explicit_target]

theorem audit_ambient_forward_orientation (s : ℂ) (hs : s ≠ 0) (x : LocalAt s) :
    audit_ambient_equiv s hs x =
      BChartTransport.translationMap s hs 1 (localReconstructEquiv s x) := rfl

theorem audit_ambient_inverse_orientation (s : ℂ) (hs : s ≠ 0) (x : LocalAt s) :
    (audit_ambient_equiv s hs).symm x =
      (localReconstructEquiv s).symm (BChartTransport.translationMap s hs (-1) x) := rfl

theorem audit_ambient_left_inverse (s : ℂ) (hs : s ≠ 0) (x : LocalAt s) :
    (audit_ambient_equiv s hs).symm (audit_ambient_equiv s hs x) = x :=
  (audit_ambient_equiv s hs).symm_apply_apply x

theorem audit_ambient_right_inverse (s : ℂ) (hs : s ≠ 0) (x : LocalAt s) :
    audit_ambient_equiv s hs ((audit_ambient_equiv s hs).symm x) = x :=
  (audit_ambient_equiv s hs).apply_symm_apply x

theorem audit_ambient_all25_explicit_normal_form (s : ℂ) (hs : s ≠ 0) :
    Ideal.map (audit_ambient_equiv s hs).toRingHom
      (Ideal.map (algebraMap A (LocalAt s)) (expectedCofactorIdeal expectedUniversal)) =
      Ideal.map (BChartTransport.toFamilyLocal s) (Ideal.span (Set.range (expectedTargetGenerators s))) := by
  change Ideal.map (BChartTransport.ambientChartEquiv s hs).toRingHom (localAmbientIdeal s) = _
  rw [BChartTransport.ambient_cofactor_normal_form s hs, audit_explicit_target]

end BChartTransportAudit

#print axioms BChartTransport.P25
#print axioms BChartTransport.v
#print axioms BChartTransport.assignment
#print axioms BChartTransport.chartMap
#print axioms BChartTransport.denominator
#print axioms BChartTransport.clearedMatrix
#print axioms BChartTransport.matrix_correspondence
#print axioms BChartTransport.denominator_correspondence
#print axioms BChartTransport.ideal_correspondence
#print axioms BChartTransport.assignment_at_family
#print axioms BChartTransport.point_composition
#print axioms BChartTransport.intoOpen
#print axioms BChartTransport.point_after_intoOpen
#print axioms BChartTransport.origin_comap_point
#print axioms BChartTransport.localChartMap
#print axioms BChartTransport.toFamilyLocal
#print axioms BChartTransport.localChartMap_source
#print axioms BChartTransport.localClearedIdeal
#print axioms BChartTransport.localExpectedIdeal
#print axioms BChartTransport.localCleared_eq_expected
#print axioms BChartTransport.denominator_value
#print axioms BChartTransport.denominator_local_unit
#print axioms BChartTransport.residue
#print axioms BChartTransport.residue_toMap
#print axioms BChartTransport.residue_polynomial
#print axioms BChartTransport.residue_surjective
#print axioms BChartTransport.unit_of_residue_ne_zero
#print axioms BChartTransport.extendAtPoint
#print axioms BChartTransport.extendAtPoint_toMap
#print axioms BChartTransport.raw
#print axioms BChartTransport.scalar
#print axioms BChartTransport.denominatorUnit
#print axioms BChartTransport.denominatorUnit_value
#print axioms BChartTransport.residue_denominatorUnit
#print axioms BChartTransport.residue_denominatorInverse
#print axioms BChartTransport.jNumerator
#print axioms BChartTransport.zNumerator
#print axioms BChartTransport.qNumerator
#print axioms BChartTransport.jValue
#print axioms BChartTransport.zValue
#print axioms BChartTransport.qValue
#print axioms BChartTransport.residue_jValue
#print axioms BChartTransport.residue_zValue
#print axioms BChartTransport.residue_qValue
#print axioms BChartTransport.shift
#print axioms BChartTransport.baseIndex
#print axioms BChartTransport.shift_at_pivot
#print axioms BChartTransport.shift_at_base
#print axioms BChartTransport.residue_shift
#print axioms BChartTransport.translationImage
#print axioms BChartTransport.translationPoly
#print axioms BChartTransport.translationImage_pivot
#print axioms BChartTransport.translationPoly_delta
#print axioms BChartTransport.delta_local_unit
#print axioms BChartTransport.translationOpen
#print axioms BChartTransport.translationOpen_matrix
#print axioms BChartTransport.translationOpen_constant
#print axioms BChartTransport.residue_translationImage
#print axioms BChartTransport.residue_translationOpen
#print axioms BChartTransport.translationMap
#print axioms BChartTransport.translationMap_raw
#print axioms BChartTransport.translationMap_scalar
#print axioms BChartTransport.translationMap_base
#print axioms BChartTransport.rationalData
#print axioms BChartTransport.translationMap_data
#print axioms BChartTransport.translationMap_denominatorUnit
#print axioms BChartTransport.translationMap_denominatorInverse
#print axioms BChartTransport.translationMap_jValue
#print axioms BChartTransport.translationMap_zValue
#print axioms BChartTransport.translationMap_qValue
#print axioms BChartTransport.translationMap_shift
#print axioms BChartTransport.localHom_ext
#print axioms BChartTransport.translationMap_zero
#print axioms BChartTransport.translationMap_add
#print axioms BChartTransport.translationEquiv
#print axioms PermanentGauge.cofactor_map
#print axioms PermanentGauge.cofactorIdeal_map
#print axioms BChartTransport.localNormalizedMatrix
#print axioms BChartTransport.translatedNormalizedMatrix
#print axioms BChartTransport.translated_entry
#print axioms BChartTransport.rowClearing
#print axioms BChartTransport.clearedMatrixData
#print axioms BChartTransport.clearedMatrix_eq_data
#print axioms BChartTransport.denominator_mul_jValue
#print axioms BChartTransport.denominator_mul_zValue
#print axioms BChartTransport.denominator_mul_qValue
#print axioms BChartTransport.row_clearing_identity
#print axioms BChartTransport.translated_cofactorIdeal
#print axioms BChartTransport.ambientChartEquiv
#print axioms BChartTransport.translation_normalized_ideal
#print axioms BChartTransport.ambient_cofactor_normal_form
#print axioms BChartTransportAudit.audit_local_chart_hom
#print axioms BChartTransportAudit.audit_translation_equiv
#print axioms BChartTransportAudit.audit_ambient_equiv
#print axioms BChartTransportAudit.audit_assignment
#print axioms BChartTransportAudit.audit_chart_substitution
#print axioms BChartTransportAudit.audit_denominator
#print axioms BChartTransportAudit.audit_actual_matrix_correspondence
#print axioms BChartTransportAudit.audit_cofactor_definition
#print axioms BChartTransportAudit.audit_all25_correspondence
#print axioms BChartTransportAudit.audit_local_hom_on_polynomials
#print axioms BChartTransportAudit.audit_denominator_residue
#print axioms BChartTransportAudit.audit_denominator_isunit
#print axioms BChartTransportAudit.audit_residue
#print axioms BChartTransportAudit.audit_extend_at_point
#print axioms BChartTransportAudit.audit_fraction_definitions
#print axioms BChartTransportAudit.audit_eight_shifts
#print axioms BChartTransportAudit.audit_actual_translation
#print axioms BChartTransportAudit.audit_translation_inverse_function
#print axioms BChartTransportAudit.audit_translation_left_inverse
#print axioms BChartTransportAudit.audit_translation_right_inverse
#print axioms BChartTransportAudit.audit_translation_group_law
#print axioms BChartTransportAudit.audit_actual_row_units
#print axioms BChartTransportAudit.audit_actual_row_identity
#print axioms BChartTransportAudit.audit_target_generator_images
#print axioms BChartTransportAudit.audit_explicit_target
#print axioms BChartTransportAudit.audit_basechanged_equality
#print axioms BChartTransportAudit.audit_ambient_forward_orientation
#print axioms BChartTransportAudit.audit_ambient_inverse_orientation
#print axioms BChartTransportAudit.audit_ambient_left_inverse
#print axioms BChartTransportAudit.audit_ambient_right_inverse
#print axioms BChartTransportAudit.audit_ambient_all25_explicit_normal_form
set_option pp.all true in
#check @BChartTransportAudit.audit_local_chart_hom
set_option pp.all true in
#check @BChartTransportAudit.audit_translation_equiv
set_option pp.all true in
#check @BChartTransportAudit.audit_ambient_all25_explicit_normal_form
#check @BChartTransport.ambient_cofactor_normal_form
run_cmd do
  for n in (← Lean.getEnv).allImportedModuleNames do
    Lean.logInfo m!"AUDIT_IMPORT {n}"
