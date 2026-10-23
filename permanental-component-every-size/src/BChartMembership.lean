import BChartAxisParameter
import AxisIdeal

/-! Full polynomial containment for the actual corrected b-chart, uniformly in
s. The proof uses exact vanishing on all three coordinate axes, not a jet or
coefficient-table hypothesis. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace BChartLocalGeometry
open MvPolynomial ConcreteLocalGeometry PrimitiveFamily

theorem axes_vanish (s : ℂ) (k : Fin 3) (r c : Fin 5) :
    axisProjection ⟨k.val + 1, by omega⟩ (equation s (r, c)) = 0 := by
  exact axes_vanish_parameter (MvPolynomial.C s + x 0) k r c

/-- Every actual full polynomial permanent belongs to the unchanged target J. -/
theorem equation_mem_target (s : ℂ) (r c : Fin 5) :
    equation s (r, c) ∈ targetIdeal := by
  apply mem_targetIdeal_of_axes_zero
  · simpa using axes_vanish s 0 r c
  · simpa using axes_vanish s 1 r c
  · simpa using axes_vanish s 2 r c

/-- No nonzero-parameter hypothesis is required for polynomial containment. -/
theorem criticalIdeal_le_targetIdeal (s : ℂ) :
    criticalIdeal s ≤ targetIdeal := by
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨r, c⟩, rfl⟩
  exact equation_mem_target s r c

end BChartLocalGeometry

#print axioms BChartLocalGeometry.axes_vanish
#print axioms BChartLocalGeometry.equation_mem_target
#print axioms BChartLocalGeometry.criticalIdeal_le_targetIdeal
