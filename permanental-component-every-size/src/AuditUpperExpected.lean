import ExceptionalUpperReconstruction

set_option autoImplicit false
namespace ExceptionalUpperAudit
open MvPowerSeries ExceptionalUpperFormal

private def expectedR {R : Type*} [CommRing R] (d h j : R) : R :=
  (d+1)*h*(j+d)*(j-1)+(d+1)*h*h*(j-d)+(d-1)*j*(j+d)
private def expectedT {R : Type*} [CommRing R] (j p c0 c1 c2 : R) : R :=
  -(j+1)*(c0-p)+(j-1)*(c1+c2)
private def expectedK {R : Type*} [CommRing R] (d h j p c0 c1 c2 : R) : R :=
  4*expectedR d h j-2*((j+1)*(j-d))*p+
  c2*(expectedT j p c0 c1 c2+2*(j-d)*(1-h)-2*(j-1)*(j+d))+
  2*(h+1)*(j-d)*c1-2*((d+1)*h+d)*expectedT j p c0 c1 c2

theorem audit_generic_quadratic {σ : Type*} (A B C : MvPowerSeries σ ℂ)
    (hA : constantCoeff A = -2) (hB : constantCoeff B = 2)
    (hC : constantCoeff C = 0) :
    ∃! j : MvPowerSeries σ ℂ, A*j^2+B*j+C = 0 ∧ constantCoeff j = 1 :=
  ExceptionalBranchHelper.exists_unique_quadratic_branch A B C hA hB hC

theorem audit_universal_polynomial {R : Type*} [CommRing R] (d h j p c0 c1 c2 : R) :
    expectedK d h j p c0 c1 c2 = ExceptionalUpper.A d h p c0 c1 c2*j^2+
      ExceptionalUpper.B d h p c0 c1 c2*j+ExceptionalUpper.C d h p c0 c1 c2 :=
  ExceptionalUpper.quadratic_identity d h j p c0 c1 c2

theorem audit_actual_ring : S = MvPowerSeries (Fin 9) ℂ := rfl

theorem audit_actual_parameters : (d,h,p,c0,c1,c2) =
    ((X 0 : S),(-1+X 1 : S),(X 2 : S),(X 3 : S),(X 4 : S),(X 5 : S)) := rfl

theorem audit_constraints_nonzero : p ≠ 0 ∧ c0 ≠ 0 ∧ c1 ≠ 0 ∧ c2 ≠ 0 := by
  have hX (r : Fin 9) : (X r : S) ≠ 0 := by
    intro he
    have hc := congrArg (coeff (Finsupp.single r 1)) he
    simp [coeff_X] at hc
  exact ⟨hX 2,hX 3,hX 4,hX 5⟩

theorem audit_constraint_variables_distinct : p ≠ c0 ∧ p ≠ c1 ∧ p ≠ c2 ∧
    c0 ≠ c1 ∧ c0 ≠ c2 ∧ c1 ≠ c2 := by
  simp [p,c0,c1,c2,x,MvPowerSeries.X_inj]

theorem audit_root_exists_unique : ∃! j : MvPowerSeries (Fin 9) ℂ,
    expectedK (X 0) (-1+X 1) j (X 2) (X 3) (X 4) (X 5) = 0 ∧
      constantCoeff j = 1 := ExceptionalUpperFormal.exists_unique_upper_root

theorem audit_actual_root :
    expectedK (X 0) (-1+X 1) root (X 2) (X 3) (X 4) (X 5) = 0 ∧
      constantCoeff root = 1 := ⟨root_equation,root_constant⟩

theorem audit_denominator : IsUnit (2*((root+1)*(root-X 0))) := denominator_unit

theorem audit_actual_inverse : (denUnit : S) * (↑(denUnit⁻¹) : S) = 1 := denUnit.mul_inv

theorem audit_reconstructed_equations :
    e*i+e+f*(-1+X 1)+f+(-1+X 1)+i = (X 2 : S) ∧
    (X 0)*(-1+X 1)+(X 0)*i+e*i+e*root+f*(-1+X 1)+f*root = (X 3 : S) ∧
    (X 0)*i+(X 0)+f*root+f+i+root = (X 4 : S) ∧
    (X 0)*(-1+X 1)+(X 0)+e*root+e+(-1+X 1)+root = (X 5 : S) :=
  ExceptionalUpperFormal.reconstruction

theorem audit_e_constant : constantCoeff e = 0 := by
  have he := congrArg constantCoeff clear_e
  norm_num [denUnit_value,ExceptionalUpper.eOut,ExceptionalCriticalFamily.eNumerator,
    ExceptionalCriticalFamily.denominator,d,h,p,c0,c1,c2,x,map_ofNat] at he
  exact he

theorem audit_f_constant : constantCoeff f = -1 := by
  have he := congrArg constantCoeff clear_f
  norm_num [denUnit_value,ExceptionalUpper.fOut,ExceptionalUpper.T,
    ExceptionalCriticalFamily.eNumerator,ExceptionalCriticalFamily.fNumerator,
    ExceptionalCriticalFamily.denominator,d,h,p,c0,c1,c2,x,map_ofNat] at he
  linear_combination (1/4 : ℂ)*he

theorem audit_i_constant : constantCoeff i = 1 := by
  have he := congrArg constantCoeff clear_i
  norm_num [denUnit_value,ExceptionalUpper.iOut,ExceptionalUpper.T,
    ExceptionalCriticalFamily.denominator,d,h,p,c0,c1,c2,x,map_ofNat] at he
  exact he

end ExceptionalUpperAudit

#print axioms ExceptionalBranchHelper.exists_unique_quadratic_branch
#print axioms ExceptionalUpper.T
#print axioms ExceptionalUpper.K
#print axioms ExceptionalUpper.A
#print axioms ExceptionalUpper.B
#print axioms ExceptionalUpper.C
#print axioms ExceptionalUpper.eOut
#print axioms ExceptionalUpper.iOut
#print axioms ExceptionalUpper.fOut
#print axioms ExceptionalUpper.quadratic_identity
#print axioms ExceptionalUpper.c1_identity
#print axioms ExceptionalUpper.c2_identity
#print axioms ExceptionalUpper.clearedP
#print axioms ExceptionalUpper.clearedC0
#print axioms ExceptionalUpper.p_identity
#print axioms ExceptionalUpper.c0_identity
#print axioms ExceptionalUpperFormal.S
#print axioms ExceptionalUpperFormal.x
#print axioms ExceptionalUpperFormal.d
#print axioms ExceptionalUpperFormal.h
#print axioms ExceptionalUpperFormal.p
#print axioms ExceptionalUpperFormal.c0
#print axioms ExceptionalUpperFormal.c1
#print axioms ExceptionalUpperFormal.c2
#print axioms ExceptionalUpperFormal.quarter
#print axioms ExceptionalUpperFormal.qa
#print axioms ExceptionalUpperFormal.qb
#print axioms ExceptionalUpperFormal.qc
#print axioms ExceptionalUpperFormal.cc_qa
#print axioms ExceptionalUpperFormal.cc_qb
#print axioms ExceptionalUpperFormal.cc_qc
#print axioms ExceptionalUpperFormal.quadratic_normalization
#print axioms ExceptionalUpperFormal.quarter_unit
#print axioms ExceptionalUpperFormal.exists_unique_upper_root
#print axioms ExceptionalUpperFormal.root
#print axioms ExceptionalUpperFormal.root_equation
#print axioms ExceptionalUpperFormal.root_constant
#print axioms ExceptionalUpperFormal.denominator_unit
#print axioms ExceptionalUpperFormal.denUnit
#print axioms ExceptionalUpperFormal.denUnit_value
#print axioms ExceptionalUpperFormal.e
#print axioms ExceptionalUpperFormal.f
#print axioms ExceptionalUpperFormal.i
#print axioms ExceptionalUpperFormal.clear_e
#print axioms ExceptionalUpperFormal.clear_f
#print axioms ExceptionalUpperFormal.clear_i
#print axioms ExceptionalUpperFormal.reconstructed_C1
#print axioms ExceptionalUpperFormal.reconstructed_C2
#print axioms ExceptionalUpperFormal.clear_P
#print axioms ExceptionalUpperFormal.clear_C0
#print axioms ExceptionalUpperFormal.reconstructed_P
#print axioms ExceptionalUpperFormal.reconstructed_C0
#print axioms ExceptionalUpperFormal.reconstruction
#print axioms ExceptionalUpperAudit.audit_generic_quadratic
#print axioms ExceptionalUpperAudit.audit_universal_polynomial
#print axioms ExceptionalUpperAudit.audit_actual_ring
#print axioms ExceptionalUpperAudit.audit_actual_parameters
#print axioms ExceptionalUpperAudit.audit_constraints_nonzero
#print axioms ExceptionalUpperAudit.audit_constraint_variables_distinct
#print axioms ExceptionalUpperAudit.audit_root_exists_unique
#print axioms ExceptionalUpperAudit.audit_actual_root
#print axioms ExceptionalUpperAudit.audit_denominator
#print axioms ExceptionalUpperAudit.audit_actual_inverse
#print axioms ExceptionalUpperAudit.audit_reconstructed_equations
#print axioms ExceptionalUpperAudit.audit_e_constant
#print axioms ExceptionalUpperAudit.audit_f_constant
#print axioms ExceptionalUpperAudit.audit_i_constant
set_option pp.all true in
#check @ExceptionalUpperAudit.audit_generic_quadratic
set_option pp.all true in
#check @ExceptionalUpperAudit.audit_root_exists_unique
set_option pp.all true in
#check @ExceptionalUpperAudit.audit_reconstructed_equations
run_cmd do
  for n in (← Lean.getEnv).allImportedModuleNames do
    Lean.logInfo m!"AUDIT_IMPORT {n}"
