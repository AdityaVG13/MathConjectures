import BChartSetup

/-! The corrected b-chart denominator in the genuine origin localization.
This does not assert any rational-chart or torus equivalence. -/
namespace BChartLocalGeometry
open MvPolynomial ConcreteLocalGeometry

/-- The denominator is literally the cleared entry (2,0) of the actual matrix. -/
theorem denominator_eq_matrix_entry (s : ℂ) :
    denominatorAt s = matrixAt s 2 0 := rfl

/-- At the origin the cleared matrix is row-scaled A(s), not A(s) itself. -/
theorem matrixAt_origin (s : ℂ) :
    (matrixAt s).map evalOrigin =
      fun i j => (![1, 1, s, s, s] i) * PrimitiveFamily.A s i j := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixAt, matrixWithParameter, evalOrigin, x, PrimitiveFamily.A]

theorem denominator_value (s : ℂ) : evalOrigin (denominatorAt s) = s := by
  simp [denominatorAt, denominatorWithParameter, evalOrigin, x]

theorem denominator_not_mem (s : ℂ) (hs : s ≠ 0) :
    denominatorAt s ∉ origin := by
  intro h
  exact hs ((denominator_value s).symm.trans (RingHom.mem_ker.mp h))

theorem denominator_unit (s : ℂ) (hs : s ≠ 0) :
    IsUnit (algebraMap P Local (denominatorAt s)) := by
  exact IsLocalization.map_units Local
    (⟨denominatorAt s, denominator_not_mem s hs⟩ : origin.primeCompl)

end BChartLocalGeometry

#print axioms BChartLocalGeometry.denominator_value
#print axioms BChartLocalGeometry.denominator_not_mem
#print axioms BChartLocalGeometry.denominator_unit

#print axioms BChartLocalGeometry.denominator_eq_matrix_entry
#print axioms BChartLocalGeometry.matrixAt_origin
