import GaugeLocalTransport
open Matrix
namespace GaugeLocalAudit

private def expectedFamily (s : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![1, 1, 1, 1, 0;
     1, 0, -1, 0, 0;
     1, -1, 1, 1, 0;
     s, 0, s, 1, 1;
     s, 0, s, 1, -1]

local instance audit_kernel_prime (s : ℂ) :
    (RingHom.ker (PermanentGauge.Coordinates.pointMap s)).IsPrime :=
  RingHom.ker_isPrime (PermanentGauge.Coordinates.pointMap s)

private abbrev ExpectedLocalAt (s : ℂ) :=
  Localization.AtPrime (RingHom.ker (PermanentGauge.Coordinates.pointMap s))

noncomputable def audit_expected_local_equiv (s : ℂ) :
    ExpectedLocalAt s ≃+* ExpectedLocalAt s :=
  PermanentGauge.Coordinates.localReconstructEquiv s

theorem audit_family_definition (s : ℂ) : PrimitiveFamily.A s = expectedFamily s := rfl

theorem audit_point_poly_definition (s : ℂ) :
    PermanentGauge.Coordinates.pointPoly s =
      MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun ij : Fin 5 × Fin 5 => expectedFamily s ij.1 ij.2) := rfl

theorem audit_evaluation_on_polynomials (s : ℂ) (p : PermanentGauge.Coordinates.P) :
    PermanentGauge.Coordinates.pointMap s
      (algebraMap PermanentGauge.Coordinates.P PermanentGauge.Coordinates.A p) =
      MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun ij : Fin 5 × Fin 5 => expectedFamily s ij.1 ij.2) p := by
  change PermanentGauge.Coordinates.pointMap s
      (algebraMap PermanentGauge.Coordinates.P PermanentGauge.Coordinates.A p) =
    PermanentGauge.Coordinates.pointPoly s p
  simp [PermanentGauge.Coordinates.pointMap]

theorem audit_evaluation_matrix (s : ℂ) (i j : Fin 5) :
    PermanentGauge.Coordinates.pointMap s (PermanentGauge.Coordinates.matrix i j) =
      expectedFamily s i j :=
  PermanentGauge.Coordinates.pointMap_matrix s i j

theorem audit_evaluation_constants (s a : ℂ) :
    PermanentGauge.Coordinates.pointMap s
      (algebraMap PermanentGauge.Coordinates.P PermanentGauge.Coordinates.A (MvPolynomial.C a)) = a := by
  simp [PermanentGauge.Coordinates.pointMap, PermanentGauge.Coordinates.pointPoly]

theorem audit_delta_evaluates_one (s : ℂ) :
    PermanentGauge.Coordinates.pointPoly s PermanentGauge.Coordinates.delta = 1 :=
  PermanentGauge.Coordinates.pointPoly_delta s

theorem audit_point_ideal_definition (s : ℂ) :
    PermanentGauge.Coordinates.pointIdeal s =
      RingHom.ker (PermanentGauge.Coordinates.pointMap s) := rfl

theorem audit_point_ideal_prime (s : ℂ) :
    (RingHom.ker (PermanentGauge.Coordinates.pointMap s)).IsPrime :=
  PermanentGauge.Coordinates.pointIdeal_prime s

theorem audit_local_type (s : ℂ) :
    PermanentGauge.Coordinates.LocalAt s = ExpectedLocalAt s := rfl

theorem audit_kernel_forward (s : ℂ) :
    (RingHom.ker (PermanentGauge.Coordinates.pointMap s)).comap
      PermanentGauge.Coordinates.forwardMap =
    RingHom.ker (PermanentGauge.Coordinates.pointMap s) :=
  PermanentGauge.Coordinates.pointIdeal_comap_forward s

theorem audit_kernel_inverse (s : ℂ) :
    (RingHom.ker (PermanentGauge.Coordinates.pointMap s)).comap
      PermanentGauge.Coordinates.inverseMap =
    RingHom.ker (PermanentGauge.Coordinates.pointMap s) :=
  PermanentGauge.Coordinates.pointIdeal_comap_inverse s

theorem audit_local_reconstruction_orientation (s : ℂ)
    (x : PermanentGauge.Coordinates.A) :
    PermanentGauge.Coordinates.localReconstructEquiv s
      (algebraMap PermanentGauge.Coordinates.A (PermanentGauge.Coordinates.LocalAt s) x) =
    algebraMap PermanentGauge.Coordinates.A (PermanentGauge.Coordinates.LocalAt s)
      (PermanentGauge.Coordinates.coordinateRingEquiv.symm x) :=
  PermanentGauge.Coordinates.localReconstruct_toMap s x

theorem audit_local_inverse_orientation (s : ℂ)
    (x : PermanentGauge.Coordinates.A) :
    (PermanentGauge.Coordinates.localReconstructEquiv s).symm
      (algebraMap PermanentGauge.Coordinates.A (PermanentGauge.Coordinates.LocalAt s) x) =
    algebraMap PermanentGauge.Coordinates.A (PermanentGauge.Coordinates.LocalAt s)
      (PermanentGauge.Coordinates.forwardMap x) := by
  apply (PermanentGauge.Coordinates.localReconstructEquiv s).injective
  rw [RingEquiv.apply_symm_apply, PermanentGauge.Coordinates.localReconstruct_toMap]
  have hx := RingHom.congr_fun PermanentGauge.Coordinates.inverse_comp_forward x
  change PermanentGauge.Coordinates.inverseMap (PermanentGauge.Coordinates.forwardMap x) = x at hx
  rw [hx]

theorem audit_local_left_inverse (s : ℂ) (x : PermanentGauge.Coordinates.LocalAt s) :
    (PermanentGauge.Coordinates.localReconstructEquiv s).symm
      (PermanentGauge.Coordinates.localReconstructEquiv s x) = x :=
  (PermanentGauge.Coordinates.localReconstructEquiv s).symm_apply_apply x

theorem audit_local_right_inverse (s : ℂ) (x : PermanentGauge.Coordinates.LocalAt s) :
    PermanentGauge.Coordinates.localReconstructEquiv s
      ((PermanentGauge.Coordinates.localReconstructEquiv s).symm x) = x :=
  (PermanentGauge.Coordinates.localReconstructEquiv s).apply_symm_apply x

private noncomputable def expectedCofactorIdeal
    (M : Matrix (Fin 5) (Fin 5) PermanentGauge.Coordinates.A) :=
  Ideal.span (Set.range (fun ij : Fin 5 × Fin 5 =>
    Matrix.permanent (fun k l : Fin 4 => M (ij.1.succAbove k) (ij.2.succAbove l))))

theorem audit_cofactor_definition
    (M : Matrix (Fin 5) (Fin 5) PermanentGauge.Coordinates.A) :
    expectedCofactorIdeal M = PermanentGauge.cofactorIdeal M := rfl

theorem audit_local_cofactor_transport (s : ℂ) :
    Ideal.map (PermanentGauge.Coordinates.localReconstructEquiv s).toRingHom
      (Ideal.map
        (algebraMap PermanentGauge.Coordinates.A (PermanentGauge.Coordinates.LocalAt s))
        (expectedCofactorIdeal PermanentGauge.Coordinates.matrix)) =
    Ideal.map
      (algebraMap PermanentGauge.Coordinates.A (PermanentGauge.Coordinates.LocalAt s))
      (expectedCofactorIdeal
        (PermanentGauge.Coordinates.clearPivots PermanentGauge.Coordinates.matrix)) := by
  simp only [audit_cofactor_definition]
  exact PermanentGauge.Coordinates.local_cofactor_transport s

end GaugeLocalAudit

#print axioms PermanentGauge.Coordinates.family_pivot
#print axioms PermanentGauge.Coordinates.pointPoly
#print axioms PermanentGauge.Coordinates.pointPoly_delta
#print axioms PermanentGauge.Coordinates.pointMap
#print axioms PermanentGauge.Coordinates.pointMap_matrix
#print axioms PermanentGauge.Coordinates.pointMap_units
#print axioms PermanentGauge.Coordinates.pointMap_rowFactor
#print axioms PermanentGauge.Coordinates.pointMap_colFactor
#print axioms PermanentGauge.Coordinates.pointMap_clearPivots
#print axioms PermanentGauge.Coordinates.pointMap_forwardImage
#print axioms PermanentGauge.Coordinates.pointMap_inverseImage
#print axioms PermanentGauge.Coordinates.pointMap_comp_forward
#print axioms PermanentGauge.Coordinates.pointMap_comp_inverse
#print axioms PermanentGauge.Coordinates.pointIdeal
#print axioms PermanentGauge.Coordinates.pointIdeal_prime
#print axioms PermanentGauge.Coordinates.pointIdeal_comap_forward
#print axioms PermanentGauge.Coordinates.pointIdeal_comap_inverse
#print axioms PermanentGauge.Coordinates.localReconstructEquiv
#print axioms PermanentGauge.Coordinates.localReconstruct_toMap
#print axioms PermanentGauge.Coordinates.localAmbientIdeal
#print axioms PermanentGauge.Coordinates.localNormalizedIdeal
#print axioms PermanentGauge.Coordinates.local_cofactor_transport
#print axioms GaugeLocalAudit.audit_kernel_prime
#print axioms GaugeLocalAudit.audit_expected_local_equiv
#print axioms GaugeLocalAudit.audit_family_definition
#print axioms GaugeLocalAudit.audit_point_poly_definition
#print axioms GaugeLocalAudit.audit_evaluation_on_polynomials
#print axioms GaugeLocalAudit.audit_evaluation_matrix
#print axioms GaugeLocalAudit.audit_evaluation_constants
#print axioms GaugeLocalAudit.audit_delta_evaluates_one
#print axioms GaugeLocalAudit.audit_point_ideal_definition
#print axioms GaugeLocalAudit.audit_point_ideal_prime
#print axioms GaugeLocalAudit.audit_local_type
#print axioms GaugeLocalAudit.audit_kernel_forward
#print axioms GaugeLocalAudit.audit_kernel_inverse
#print axioms GaugeLocalAudit.audit_local_reconstruction_orientation
#print axioms GaugeLocalAudit.audit_local_inverse_orientation
#print axioms GaugeLocalAudit.audit_local_left_inverse
#print axioms GaugeLocalAudit.audit_local_right_inverse
#print axioms GaugeLocalAudit.audit_cofactor_definition
#print axioms GaugeLocalAudit.audit_local_cofactor_transport
#check @PermanentGauge.Coordinates.localReconstructEquiv
#check @PermanentGauge.Coordinates.local_cofactor_transport
#check @PermanentGauge.Coordinates.pointMap_comp_forward
#check @PermanentGauge.Coordinates.pointMap_comp_inverse
set_option pp.all true in
#check @GaugeLocalAudit.audit_expected_local_equiv
set_option pp.all true in
#check @GaugeLocalAudit.audit_local_cofactor_transport
#print Localization.AtPrime
run_cmd do
  for n in (← Lean.getEnv).allImportedModuleNames do
    Lean.logInfo m!"AUDIT_IMPORT {n}"
