import ExceptionalBranchFromRoot
import FormalSquareRoot

set_option autoImplicit false
namespace ExceptionalBranch

/-- All-orders existence and uniqueness for the actual exceptional critical
branch relation, with d, h+1 and a independent formal parameters. -/
theorem exists_unique_branch : ∃! j : Series,
    ExceptionalCriticalFamily.relation d h j = 0 ∧ MvPowerSeries.constantCoeff j = 1 := by
  obtain ⟨w, hw, _⟩ := ExceptionalBranchHelper.exists_unique_square_root_four
    (discriminant d h) cc_discriminant
  refine ⟨branchCandidate w, ⟨candidate_relation w hw.1, candidate_constant w hw.2⟩, ?_⟩
  intro k hk
  exact branch_unique k (branchCandidate w) hk.2 (candidate_constant w hw.2)
    hk.1 (candidate_relation w hw.1)

noncomputable def branch : Series := Classical.choose exists_unique_branch.exists
theorem branch_relation : ExceptionalCriticalFamily.relation d h branch = 0 :=
  (Classical.choose_spec exists_unique_branch.exists).1
theorem branch_constant : MvPowerSeries.constantCoeff branch = 1 :=
  (Classical.choose_spec exists_unique_branch.exists).2

theorem branch_denominator_unit : IsUnit (ExceptionalCriticalFamily.denominator d branch) := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  norm_num [ExceptionalCriticalFamily.denominator, branch_constant]

/-- An actual all-orders critical matrix over C[[d,h+1,a]], not a finite jet
and not a statement conditional on an unconstructed branch. -/
noncomputable def formalCriticalMatrix : Matrix (Fin 5) (Fin 5) Series :=
  ExceptionalCriticalFamily.matrix d h branch (MvPowerSeries.X 2)

theorem formalCriticalMatrix_cofactors_zero : ∀ i j : Fin 5,
    (formalCriticalMatrix.submatrix i.succAbove j.succAbove).permanent = 0 :=
  ExceptionalCriticalFamily.zero_relation_critical d h branch (MvPowerSeries.X 2) branch_relation

#print axioms exists_unique_branch
#print axioms branch_denominator_unit
#print axioms formalCriticalMatrix_cofactors_zero
end ExceptionalBranch
