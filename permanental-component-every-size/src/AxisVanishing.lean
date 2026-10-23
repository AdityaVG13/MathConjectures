import AxisProjectionSetup
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace ConcreteLocalGeometry
open PrimitiveFamily

theorem axes_vanish (k : Fin 3) (r c : Fin 5) : axisProjection ⟨k.val+1, by omega⟩ (equation (r,c)) = 0 := by
  have hc2 : (MvPolynomial.C (2 : ℂ) : P) = 2 := by exact MvPolynomial.C_eq_coe_nat 2
  fin_cases k <;> fin_cases r <;> fin_cases c
  all_goals unfold equation
  all_goals rw [expand4]
  all_goals simp [Fin.sum_univ_succ, Fin.prod_univ_succ, enumerate4,
    p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,
    Matrix.submatrix,N,Fin.succAbove,jn,kn,zn,den,da,dq,dd,t,x,axisProjection]
  all_goals simp only [hc2]
  all_goals ring
#print axioms axes_vanish
end ConcreteLocalGeometry
