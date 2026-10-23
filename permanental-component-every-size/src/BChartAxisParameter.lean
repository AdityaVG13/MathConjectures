import BChartSetup
import AxisProjectionSetup

/-! Exact all-axis identities with an arbitrary polynomial parameter.
Keeping the projected parameter abstract avoids expanding s+x0 unnecessarily. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace BChartLocalGeometry
open MvPolynomial ConcreteLocalGeometry PrimitiveFamily

private theorem bind_two (f : Fin 16 → P) : bind₁ f (2 : P) = 2 := by
  have h : (MvPolynomial.C (2 : ℂ) : P) = 2 := MvPolynomial.C_eq_coe_nat 2
  rw [← h, bind₁_C_right]

theorem axes_vanish_parameter (T : P) (k : Fin 3) (r c : Fin 5) :
    axisProjection ⟨k.val + 1, by omega⟩
      (((matrixWithParameter T).submatrix r.succAbove c.succAbove).permanent) = 0 := by
  fin_cases k <;> fin_cases r <;> fin_cases c
  all_goals rw [expand4]
  all_goals simp [Fin.sum_univ_succ, Fin.prod_univ_succ, enumerate4,
    p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,
    Matrix.submatrix, matrixWithParameter, Fin.succAbove, x, axisProjection]
  all_goals try simp only [bind_two]
  all_goals ring

end BChartLocalGeometry
#print axioms BChartLocalGeometry.axes_vanish_parameter
