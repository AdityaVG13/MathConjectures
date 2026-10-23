import ExceptionalBranchQuadratic

set_option autoImplicit false
namespace ExceptionalBranch

theorem twice_alpha_unit : IsUnit (2*alpha d h) := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  norm_num [map_ofNat]
noncomputable def denominatorUnit : Seriesˣ := twice_alpha_unit.unit
theorem denominatorUnit_value : (denominatorUnit : Series) = 2*alpha d h :=
  twice_alpha_unit.unit_spec

/-- The root with residue j=1 uses the negative square-root sign. -/
noncomputable def branchCandidate (w : Series) : Series :=
  -(beta d h+w) * (↑(denominatorUnit⁻¹) : Series)

theorem candidate_clearing (w : Series) :
    2*alpha d h*branchCandidate w = -(beta d h+w) := by
  rw [← denominatorUnit_value]
  simp [branchCandidate, mul_comm]

theorem candidate_constant (w : Series) (hw : MvPowerSeries.constantCoeff w = 2) :
    MvPowerSeries.constantCoeff (branchCandidate w) = 1 := by
  have he := congrArg MvPowerSeries.constantCoeff (candidate_clearing w)
  simp only [map_mul, map_ofNat, cc_alpha, map_neg, map_add, cc_beta, hw] at he
  linear_combination -(1/4 : ℂ)*he

theorem candidate_relation (w : Series) (hw : w^2 = discriminant d h) :
    ExceptionalCriticalFamily.relation d h (branchCandidate w) = 0 := by
  have hs : 2*alpha d h*branchCandidate w+beta d h = -w := by
    rw [candidate_clearing]
    ring
  have he := complete_square d h (branchCandidate w)
  rw [hs, neg_sq, hw, sub_self] at he
  have hu : IsUnit (4*alpha d h) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    norm_num [map_ofNat]
  exact hu.mul_left_cancel (by simpa using he.symm)

/-- Conditional only on a square-root input; the separate existence module
will discharge that input via the actual discriminant's constant coefficient. -/
theorem candidate_critical (w : Series) (hw : w^2 = discriminant d h) :
    ∀ i j : Fin 5,
      ((ExceptionalCriticalFamily.matrix d h (branchCandidate w) (MvPowerSeries.X 2)).submatrix
        i.succAbove j.succAbove).permanent = 0 :=
  ExceptionalCriticalFamily.zero_relation_critical d h (branchCandidate w)
    (MvPowerSeries.X 2) (candidate_relation w hw)

theorem candidate_denominator_unit (w : Series)
    (hw : MvPowerSeries.constantCoeff w = 2) :
    IsUnit (ExceptionalCriticalFamily.denominator d (branchCandidate w)) := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  norm_num [ExceptionalCriticalFamily.denominator, candidate_constant w hw]

#print axioms candidate_relation
#print axioms candidate_critical
#print axioms candidate_denominator_unit
end ExceptionalBranch
