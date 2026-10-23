import ExceptionalBranchExistence
import ExceptionalIntrinsicElimination

namespace ExceptionalBranchAudit
open Matrix MvPowerSeries

private def expectedRelation {R : Type*} [CommRing R] (d h j : R) : R :=
  (d+1)*h*(j+d)*(j-1)+(d+1)*h*h*(j-d)+(d-1)*j*(j+d)

private def expectedDenominator {R : Type*} [CommRing R] (d j : R) := (j+1)*(j-d)
private def expectedE {R : Type*} [CommRing R] (d h j : R) := -((d+1)*h+d+j)
private def expectedF {R : Type*} [CommRing R] (d h j : R) :=
  (d-1)*(j+d)*(j+1)-expectedE d h j*(j-d)
private def expectedI {R : Type*} [CommRing R] (d h j : R) :=
  -(j-1)*(j+d)*(j+1)-h*expectedDenominator d j

private def expectedMatrix {R : Type*} [CommRing R] (d h j a : R) : Matrix (Fin 5) (Fin 5) R :=
  !![1,1,1,1,a;
     expectedDenominator d j,expectedE d h j*(j-d),expectedF d h j,
       expectedDenominator d j*d,expectedDenominator d j*d*a;
     expectedDenominator d j,expectedDenominator d j*h,expectedI d h j,
       expectedDenominator d j*j,expectedDenominator d j*j*a;
     0,0,0,1,1; 0,0,0,1,-1]

theorem audit_quadratic {R : Type*} [CommRing R] (d h j : R) :
    expectedRelation d h j = ((d+1)*h+d-1)*j^2 +
      ((d+1)*h*(d-1)+(d+1)*h*h+d*(d-1))*j - d*(d+1)*h*(1+h) := by
  have he := ExceptionalBranch.relation_quadratic d h j
  simpa [expectedRelation, ExceptionalBranch.alpha, ExceptionalBranch.beta,
    ExceptionalBranch.gamma, ExceptionalCriticalFamily.relation, sub_eq_add_neg] using he

theorem audit_actual_series : ExceptionalBranch.Series = MvPowerSeries (Fin 3) ℂ := rfl

theorem audit_branch_exists_unique : ∃! j : MvPowerSeries (Fin 3) ℂ,
    expectedRelation (X 0) (-1+X 1) j = 0 ∧ constantCoeff j = 1 :=
  ExceptionalBranch.exists_unique_branch

theorem audit_selected_branch_relation :
    expectedRelation (X 0) (-1+X 1) ExceptionalBranch.branch = 0 :=
  ExceptionalBranch.branch_relation

theorem audit_selected_branch_constant : constantCoeff ExceptionalBranch.branch = 1 :=
  ExceptionalBranch.branch_constant

theorem audit_actual_denominator_unit :
    IsUnit ((ExceptionalBranch.branch+1)*(ExceptionalBranch.branch-X 0)) :=
  ExceptionalBranch.branch_denominator_unit

theorem audit_actual_matrix : ExceptionalBranch.formalCriticalMatrix =
    expectedMatrix (X 0) (-1+X 1) ExceptionalBranch.branch (X 2) := rfl

theorem audit_all25_actual_cofactors (i j : Fin 5) :
    Matrix.permanent (fun r c : Fin 4 =>
      expectedMatrix (X 0) (-1+X 1) ExceptionalBranch.branch (X 2)
        (i.succAbove r) (j.succAbove c)) = 0 :=
  ExceptionalBranch.formalCriticalMatrix_cofactors_zero i j

theorem audit_cleared_basepoint :
    (fun i j => constantCoeff (ExceptionalBranch.formalCriticalMatrix i j)) =
      fun i j => (![1,2,2,1,1] i : ℂ) * PrimitiveFamily.A 0 i j := by
  have hbase := ExceptionalCriticalFamily.cleared_basepoint (R := ℂ)
  rw [← hbase]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ExceptionalBranch.formalCriticalMatrix, ExceptionalCriticalFamily.matrix,
      ExceptionalCriticalFamily.denominator, ExceptionalCriticalFamily.eNumerator,
      ExceptionalCriticalFamily.fNumerator, ExceptionalCriticalFamily.iNumerator,
      ExceptionalBranch.branch_constant, ExceptionalBranch.cc_d, ExceptionalBranch.cc_h]

theorem audit_selected_root_sign (w : ExceptionalBranch.Series) :
    (2*ExceptionalBranch.alpha ExceptionalBranch.d ExceptionalBranch.h)*
      ExceptionalBranch.branchCandidate w =
      -(ExceptionalBranch.beta ExceptionalBranch.d ExceptionalBranch.h+w) :=
  ExceptionalBranch.candidate_clearing w

theorem audit_conditional_root_discharged (w : ExceptionalBranch.Series)
    (hw : w^2=ExceptionalBranch.discriminant ExceptionalBranch.d ExceptionalBranch.h)
    (hc : constantCoeff w=2) :
    ExceptionalBranch.branchCandidate w = ExceptionalBranch.branch :=
  ExceptionalBranch.branch_unique _ _ (ExceptionalBranch.candidate_constant w hc)
    ExceptionalBranch.branch_constant (ExceptionalBranch.candidate_relation w hw)
    ExceptionalBranch.branch_relation

theorem audit_intrinsic_constraints {R : Type*} [CommRing R] (d h j e f i : R)
    (h2 : IsUnit (2 : R)) (hp : IsUnit (j+1)) (hm : IsUnit (j-d)) :
    (e*i+e+f*h+f+h+i = 0 ∧
     d*h+d*i+e*i+e*j+f*h+f*j = 0 ∧
     d*i+d+f*j+f+i+j = 0 ∧
     d*h+d+e*j+e+h+j = 0) ↔
    ((j+1)*e + ((d+1)*h+d+j) = 0 ∧
     (j-d)*(i+h)+(j-1)*(j+d) = 0 ∧
     ((j+1)*(j-d))*f - ((d-1)*(j+d)*(j+1)+((d+1)*h+d+j)*(j-d)) = 0 ∧
     expectedRelation d h j = 0) := by
  have he := ExceptionalIntrinsic.constraints_iff d h j e f i h2 hp hm
  simp only [ExceptionalIntrinsic.P, ExceptionalIntrinsic.C0, ExceptionalIntrinsic.C1,
    ExceptionalIntrinsic.C2, ExceptionalIntrinsic.E, ExceptionalIntrinsic.I,
    ExceptionalIntrinsic.F, ExceptionalCriticalFamily.eNumerator,
    ExceptionalCriticalFamily.fNumerator, ExceptionalCriticalFamily.denominator,
    expectedRelation, ExceptionalCriticalFamily.relation] at he ⊢
  simpa only [neg_mul, sub_neg_eq_add] using he

end ExceptionalBranchAudit

#print axioms ExceptionalBranch.alpha
#print axioms ExceptionalBranch.beta
#print axioms ExceptionalBranch.gamma
#print axioms ExceptionalBranch.discriminant
#print axioms ExceptionalBranch.relation_quadratic
#print axioms ExceptionalBranch.complete_square
#print axioms ExceptionalBranch.difference_factor
#print axioms ExceptionalBranch.Series
#print axioms ExceptionalBranch.d
#print axioms ExceptionalBranch.h
#print axioms ExceptionalBranch.cc_d
#print axioms ExceptionalBranch.cc_h
#print axioms ExceptionalBranch.cc_alpha
#print axioms ExceptionalBranch.cc_beta
#print axioms ExceptionalBranch.cc_gamma
#print axioms ExceptionalBranch.cc_discriminant
#print axioms ExceptionalBranch.alpha_unit
#print axioms ExceptionalBranch.branch_unique
#print axioms ExceptionalBranch.twice_alpha_unit
#print axioms ExceptionalBranch.denominatorUnit
#print axioms ExceptionalBranch.denominatorUnit_value
#print axioms ExceptionalBranch.branchCandidate
#print axioms ExceptionalBranch.candidate_clearing
#print axioms ExceptionalBranch.candidate_constant
#print axioms ExceptionalBranch.candidate_relation
#print axioms ExceptionalBranch.candidate_critical
#print axioms ExceptionalBranch.candidate_denominator_unit
#print axioms ExceptionalBranch.exists_unique_branch
#print axioms ExceptionalBranch.branch
#print axioms ExceptionalBranch.branch_relation
#print axioms ExceptionalBranch.branch_constant
#print axioms ExceptionalBranch.branch_denominator_unit
#print axioms ExceptionalBranch.formalCriticalMatrix
#print axioms ExceptionalBranch.formalCriticalMatrix_cofactors_zero
#print axioms ExceptionalIntrinsic.P
#print axioms ExceptionalIntrinsic.C0
#print axioms ExceptionalIntrinsic.C1
#print axioms ExceptionalIntrinsic.C2
#print axioms ExceptionalIntrinsic.E
#print axioms ExceptionalIntrinsic.I
#print axioms ExceptionalIntrinsic.F
#print axioms ExceptionalIntrinsic.e_identity
#print axioms ExceptionalIntrinsic.i_identity
#print axioms ExceptionalIntrinsic.i_clearing
#print axioms ExceptionalIntrinsic.f_identity
#print axioms ExceptionalIntrinsic.relation_identity
#print axioms ExceptionalIntrinsic.constraints_iff
#print axioms ExceptionalBranchAudit.audit_quadratic
#print axioms ExceptionalBranchAudit.audit_actual_series
#print axioms ExceptionalBranchAudit.audit_branch_exists_unique
#print axioms ExceptionalBranchAudit.audit_selected_branch_relation
#print axioms ExceptionalBranchAudit.audit_selected_branch_constant
#print axioms ExceptionalBranchAudit.audit_actual_denominator_unit
#print axioms ExceptionalBranchAudit.audit_actual_matrix
#print axioms ExceptionalBranchAudit.audit_all25_actual_cofactors
#print axioms ExceptionalBranchAudit.audit_cleared_basepoint
#print axioms ExceptionalBranchAudit.audit_selected_root_sign
#print axioms ExceptionalBranchAudit.audit_conditional_root_discharged
#print axioms ExceptionalBranchAudit.audit_intrinsic_constraints
set_option pp.all true in
#check @ExceptionalBranchAudit.audit_branch_exists_unique
set_option pp.all true in
#check @ExceptionalBranchAudit.audit_all25_actual_cofactors
#check @ExceptionalBranchAudit.audit_intrinsic_constraints
run_cmd do
  for n in (← Lean.getEnv).allImportedModuleNames do
    Lean.logInfo m!"AUDIT_IMPORT {n}"
