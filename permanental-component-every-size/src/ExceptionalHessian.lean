import ExceptionalCofactorDerivative
import ExceptionalStationaryJacobian
import ParametricMatrix

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace ExceptionalHessian
open ConcreteLocalGeometry ParametricLocalGeometry ExceptionalStationaryJacobian
open PrimitiveFamily MvPolynomial

def errorIndex : Fin 12 → Fin 16 := ![4,5,6,7,8,9,10,11,12,13,14,15]
noncomputable def potential : P := (translatedN 0).permanent
noncomputable def factor (i : Fin 12) : P :=
  if i.val<6 then 1 else translatedN 0 3 3

theorem entry_derivative (i : Fin 12) (r c : Fin 5) :
    pderiv (errorIndex i) (translatedN 0 r c) =
      if r=(principalPairs i).1 ∧ c=(principalPairs i).2 then factor i else 0 := by
  simp only [factor,translatedN_eq_matrixWithParameter]
  fin_cases i <;> fin_cases r <;> fin_cases c <;>
    norm_num [matrixWithParameter,x,errorIndex,principalPairs]

theorem potential_gradient (i : Fin 12) :
    pderiv (errorIndex i) potential = factor i * translatedEquation 0 (principalPairs i) := by
  exact ExceptionalCofactorDerivative.permanent_derivative_single _ _ _ _ _
    (entry_derivative i)

theorem factor_value (i : Fin 12) : evalOrigin (factor i) = 1 := by
  fin_cases i <;> norm_num [factor,parametricEntryJetTable]

theorem cofactor_value (r c : Fin 5) : evalOrigin (translatedEquation 0 (r,c)) = 0 := by
  fin_cases r <;> fin_cases c
  all_goals unfold translatedEquation
  all_goals simp only [expand4]
  all_goals norm_num [Fin.sum_univ_succ,Fin.prod_univ_succ,enumerate4,
    p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,
    Matrix.submatrix,Fin.succAbove,parametricEntryJetTable]

noncomputable def hessianBlock : Matrix (Fin 12) (Fin 12) ℂ :=
  fun i j => firstDerivative (errorIndex j) (pderiv (errorIndex i) potential)

theorem firstVector_eq (f : P) (j : Fin 12) :
    firstVector f j = firstDerivative (errorIndex j) f := by
  fin_cases j <;> rfl

theorem hessian_eq_stationary : hessianBlock = stationaryJacobian := by
  ext i j
  have hz := cofactor_value (principalPairs i).1 (principalPairs i).2
  change evalOrigin (translatedEquation 0 (principalPairs i)) = 0 at hz
  simp only [hessianBlock,potential_gradient,first_mul,
    hz,factor_value,mul_zero,one_mul,zero_add]
  exact (firstVector_eq _ j).symm

theorem hessian_rank : hessianBlock.rank = 12 := by
  rw [hessian_eq_stationary]
  exact actual_rank
end ExceptionalHessian
#print axioms ExceptionalHessian.entry_derivative
#print axioms ExceptionalHessian.potential_gradient
#print axioms ExceptionalHessian.hessian_eq_stationary
#print axioms ExceptionalHessian.hessian_rank
