import ExceptionalUpperInversePolynomial
import ExceptionalQuadraticInverse

set_option autoImplicit false
namespace ExceptionalUpperFormal
open MvPowerSeries
abbrev S := MvPowerSeries (Fin 9) ℂ
noncomputable def x (i : Fin 9) : S := X i
noncomputable def d : S := x 0
noncomputable def h : S := -1+x 1
noncomputable def p : S := x 2
noncomputable def c0 : S := x 3
noncomputable def c1 : S := x 4
noncomputable def c2 : S := x 5
noncomputable def quarter : S := C (1/4 : ℂ)
noncomputable def qa : S := quarter*ExceptionalUpper.A d h p c0 c1 c2
noncomputable def qb : S := quarter*ExceptionalUpper.B d h p c0 c1 c2
noncomputable def qc : S := quarter*ExceptionalUpper.C d h p c0 c1 c2

@[simp] theorem cc_qa : constantCoeff qa = -2 := by
  norm_num [qa,quarter,ExceptionalUpper.A,ExceptionalBranch.alpha,d,h,p,c0,c1,c2,x,map_ofNat]
@[simp] theorem cc_qb : constantCoeff qb = 2 := by
  norm_num [qb,quarter,ExceptionalUpper.B,ExceptionalBranch.beta,d,h,p,c0,c1,c2,x,map_ofNat]
@[simp] theorem cc_qc : constantCoeff qc = 0 := by
  norm_num [qc,quarter,ExceptionalUpper.C,ExceptionalBranch.gamma,d,h,p,c0,c1,c2,x,map_ofNat]

theorem quadratic_normalization (j : S) :
    qa*j^2+qb*j+qc = quarter*ExceptionalUpper.K d h j p c0 c1 c2 := by
  rw [ExceptionalUpper.quadratic_identity]
  unfold qa qb qc
  ring

theorem quarter_unit : IsUnit quarter := by
  rw [isUnit_iff_constantCoeff,isUnit_iff_ne_zero]
  norm_num [quarter]

/-- All-orders existence and uniqueness with independent, nonzero formal
constraint values. This is a root construction, not yet the coordinate equivalence. -/
theorem exists_unique_upper_root : ∃! j : S,
    ExceptionalUpper.K d h j p c0 c1 c2 = 0 ∧ constantCoeff j = 1 := by
  obtain ⟨j,hj,hunique⟩ := ExceptionalBranchHelper.exists_unique_quadratic_branch qa qb qc cc_qa cc_qb cc_qc
  have hjK : ExceptionalUpper.K d h j p c0 c1 c2 = 0 := by
    have he := hj.1
    rw [quadratic_normalization] at he
    exact quarter_unit.mul_left_cancel (by simpa using he)
  refine ⟨j,⟨hjK,hj.2⟩,?_⟩
  intro k hk
  apply hunique k
  refine ⟨?_,hk.2⟩
  rw [quadratic_normalization,hk.1,mul_zero]

noncomputable def root : S := Classical.choose exists_unique_upper_root.exists
theorem root_equation : ExceptionalUpper.K d h root p c0 c1 c2 = 0 :=
  (Classical.choose_spec exists_unique_upper_root.exists).1
@[simp] theorem root_constant : constantCoeff root = 1 :=
  (Classical.choose_spec exists_unique_upper_root.exists).2

theorem denominator_unit : IsUnit (2*ExceptionalCriticalFamily.denominator d root) := by
  rw [isUnit_iff_constantCoeff,isUnit_iff_ne_zero]
  norm_num [ExceptionalCriticalFamily.denominator,d,x,map_ofNat]

#print axioms exists_unique_upper_root
#print axioms denominator_unit
end ExceptionalUpperFormal
