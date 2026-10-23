import BChartExplicitNormalForm

namespace RawAmbientAudit
open Matrix MvPolynomial PermanentGauge.Coordinates

private def expectedFamily (s : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![1,1,1,1,0; 1,0,-1,0,0; 1,-1,1,1,0; s,0,s,1,1; s,0,s,1,-1]
private noncomputable def expectedEvaluation (s : ℂ) : P →+* ℂ :=
  eval₂Hom (RingHom.id ℂ) (fun ij => expectedFamily s ij.1 ij.2)
private noncomputable def expectedKernel (s : ℂ) : Ideal P := RingHom.ker (expectedEvaluation s)
local instance expectedKernel_prime (s : ℂ) : (expectedKernel s).IsPrime :=
  RingHom.ker_isPrime (expectedEvaluation s)
private abbrev ExpectedRawLocal (s : ℂ) := Localization.AtPrime (expectedKernel s)

private noncomputable def expectedGenerators (s : ℂ) : Fin 15 → P :=
  ![X (1,1),X (1,2)+1,X (1,4),X (2,2)-1,X (2,3)-1,X (2,4),
    X (3,0)-C s,X (2,1)+1,X (3,2)-C s,X (4,1),X (4,2)-C s,X (4,4)+1,
    X (0,4)*X (1,3),X (0,4)*X (3,1),X (1,3)*X (3,1)]
private noncomputable def expectedRawCofactors : Ideal P :=
  Ideal.span (Set.range (fun ij : Fin 5 × Fin 5 =>
    Matrix.permanent (fun k l : Fin 4 => (X (ij.1.succAbove k,ij.2.succAbove l) : P))))

noncomputable def audit_raw_local_equiv (s : ℂ) : ExpectedRawLocal s ≃ₐ[P] LocalAt s :=
  BChartTransport.rawLocalEquiv s
noncomputable def audit_raw_ambient_equiv (s : ℂ) (hs : s ≠ 0) :
    ExpectedRawLocal s ≃+* LocalAt s := BChartTransport.rawAmbientChartEquiv s hs

theorem audit_evaluation_definition (s : ℂ) : pointPoly s = expectedEvaluation s := rfl

theorem audit_raw_kernel (s : ℂ) : BChartTransport.rawPointIdeal s = expectedKernel s := rfl

theorem audit_localization_instance (s : ℂ) : IsLocalization.AtPrime (LocalAt s) (expectedKernel s) :=
  BChartTransport.rawLocalization s

theorem audit_raw_type (s : ℂ) : BChartTransport.RawLocalAt s = ExpectedRawLocal s := rfl

theorem audit_raw_local_polynomials (s : ℂ) (p : P) :
    audit_raw_local_equiv s (algebraMap P (ExpectedRawLocal s) p) =
      BChartTransport.toFamilyLocal s p := BChartTransport.rawLocalEquiv_polynomial s p

theorem audit_raw_local_left_inverse (s : ℂ) (x : ExpectedRawLocal s) :
    (audit_raw_local_equiv s).symm (audit_raw_local_equiv s x) = x :=
  (audit_raw_local_equiv s).symm_apply_apply x

theorem audit_raw_local_right_inverse (s : ℂ) (x : LocalAt s) :
    audit_raw_local_equiv s ((audit_raw_local_equiv s).symm x) = x :=
  (audit_raw_local_equiv s).apply_symm_apply x

theorem audit_raw_cofactor_definition :
    expectedRawCofactors = PermanentGauge.cofactorIdeal BChartTransport.rawMatrix := rfl

theorem audit_explicit_generators (s : ℂ) :
    BChartTransport.explicitGenerator s = expectedGenerators s := rfl

theorem audit_raw_composition (s : ℂ) (hs : s ≠ 0) (x : ExpectedRawLocal s) :
    audit_raw_ambient_equiv s hs x =
      BChartTransport.translationMap s hs 1
        (localReconstructEquiv s (audit_raw_local_equiv s x)) := rfl

theorem audit_raw_inverse_composition (s : ℂ) (hs : s ≠ 0) (x : LocalAt s) :
    (audit_raw_ambient_equiv s hs).symm x =
      (audit_raw_local_equiv s).symm
        ((localReconstructEquiv s).symm (BChartTransport.translationMap s hs (-1) x)) := rfl

theorem audit_raw_left_inverse (s : ℂ) (hs : s ≠ 0) (x : ExpectedRawLocal s) :
    (audit_raw_ambient_equiv s hs).symm (audit_raw_ambient_equiv s hs x) = x :=
  (audit_raw_ambient_equiv s hs).symm_apply_apply x

theorem audit_raw_right_inverse (s : ℂ) (hs : s ≠ 0) (x : LocalAt s) :
    audit_raw_ambient_equiv s hs ((audit_raw_ambient_equiv s hs).symm x) = x :=
  (audit_raw_ambient_equiv s hs).apply_symm_apply x

theorem audit_original_all25_explicit_target (s : ℂ) (hs : s ≠ 0) :
    Ideal.map (audit_raw_ambient_equiv s hs).toRingHom
      (Ideal.map (algebraMap P (ExpectedRawLocal s)) expectedRawCofactors) =
      Ideal.map (BChartTransport.toFamilyLocal s)
        (Ideal.span (Set.range (expectedGenerators s))) :=
  BChartTransport.raw_ambient_explicit_normal_form s hs

theorem audit_parameter_one :
    Ideal.map (audit_raw_ambient_equiv 1 one_ne_zero).toRingHom
      (Ideal.map (algebraMap P (ExpectedRawLocal 1)) expectedRawCofactors) =
      Ideal.map (BChartTransport.toFamilyLocal 1)
        (Ideal.span (Set.range (expectedGenerators 1))) :=
  audit_original_all25_explicit_target 1 one_ne_zero

end RawAmbientAudit

#print axioms BChartTransport.rawPointIdeal
#print axioms BChartTransport.rawPointIdeal_prime
#print axioms BChartTransport.RawLocalAt
#print axioms BChartTransport.rawPointIdeal_comap
#print axioms BChartTransport.rawLocalization
#print axioms BChartTransport.rawLocalEquiv
#print axioms BChartTransport.rawLocalEquiv_polynomial
#print axioms BChartTransport.rawMatrix
#print axioms BChartTransport.rawLocalCofactorIdeal
#print axioms BChartTransport.rawLocalEquiv_cofactorIdeal
#print axioms BChartTransport.rawAmbientChartEquiv
#print axioms BChartTransport.raw_ambient_cofactor_normal_form
#print axioms BChartTransport.explicitGenerator
#print axioms BChartTransport.explicitTarget
#print axioms BChartTransport.explicitGenerator_correspondence
#print axioms BChartTransport.explicitTarget_correspondence
#print axioms BChartTransport.raw_ambient_explicit_normal_form
#print axioms RawAmbientAudit.audit_raw_local_equiv
#print axioms RawAmbientAudit.audit_raw_ambient_equiv
#print axioms RawAmbientAudit.audit_evaluation_definition
#print axioms RawAmbientAudit.audit_raw_kernel
#print axioms RawAmbientAudit.audit_localization_instance
#print axioms RawAmbientAudit.audit_raw_type
#print axioms RawAmbientAudit.audit_raw_local_polynomials
#print axioms RawAmbientAudit.audit_raw_local_left_inverse
#print axioms RawAmbientAudit.audit_raw_local_right_inverse
#print axioms RawAmbientAudit.audit_raw_cofactor_definition
#print axioms RawAmbientAudit.audit_explicit_generators
#print axioms RawAmbientAudit.audit_raw_composition
#print axioms RawAmbientAudit.audit_raw_inverse_composition
#print axioms RawAmbientAudit.audit_raw_left_inverse
#print axioms RawAmbientAudit.audit_raw_right_inverse
#print axioms RawAmbientAudit.audit_original_all25_explicit_target
#print axioms RawAmbientAudit.audit_parameter_one
#print axioms RawAmbientAudit.expectedKernel_prime
set_option pp.all true in
#check @RawAmbientAudit.audit_raw_local_equiv
set_option pp.all true in
#check @RawAmbientAudit.audit_original_all25_explicit_target
#check @BChartTransport.raw_ambient_explicit_normal_form
run_cmd do
  for n in (← Lean.getEnv).allImportedModuleNames do
    Lean.logInfo m!"AUDIT_IMPORT {n}"
