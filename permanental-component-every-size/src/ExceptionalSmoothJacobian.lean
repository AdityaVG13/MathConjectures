import ExceptionalCriticalFamily
import Mathlib.Algebra.MvPolynomial.PDeriv

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ExceptionalSmoothJacobian
variable {R : Type*} [CommRing R]
def top (d h e f i j : R) : Matrix (Fin 3) (Fin 4) R :=
  !![1,1,1,1;1,e,f,d;1,h,i,j]
def constraints (d h e f i j : R) : Fin 4 → R :=
  ![e*i+e+f*h+f+h+i,
    d*h+d*i+e*i+e*j+f*h+f*j,
    d*i+d+f*j+f+i+j,
    d*h+d+e*j+e+h+j]
def omitted : Fin 4 → Fin 4 := ![3,0,1,2]

theorem constraints_are_permanents (d h e f i j : R) (k : Fin 4) :
    constraints d h e f i j k =
      ((top d h e f i j).submatrix id (omitted k).succAbove).permanent := by
  fin_cases k
  all_goals rw [PrimitiveFamily.expand3]
  all_goals norm_num [Fin.sum_univ_succ,Fin.prod_univ_succ,PrimitiveFamily.enumerate3,
    PrimitiveFamily.q0,PrimitiveFamily.q1,PrimitiveFamily.q2,
    PrimitiveFamily.q3,PrimitiveFamily.q4,PrimitiveFamily.q5,
    Matrix.submatrix,Fin.succAbove,top,constraints,omitted]
  all_goals ring

open MvPolynomial
abbrev P := MvPolynomial (Fin 4) ℚ
noncomputable def system : Fin 4 → P :=
  constraints 0 (-1) (X 0) (X 1) (X 2) (X 3)
def base : Fin 4 → ℚ := ![0,-1,1,1]
noncomputable def jacobian : Matrix (Fin 4) (Fin 4) ℚ :=
  fun r c => eval base (pderiv c (system r))

theorem jacobian_formula : jacobian =
    !![2,0,1,0;2,0,0,-1;0,2,1,0;2,0,0,1] := by
  ext r c
  fin_cases r <;> fin_cases c <;> norm_num [jacobian,system,constraints,base]

theorem jacobian_determinant : jacobian.det = 8 := by
  rw [jacobian_formula]
  norm_num [Matrix.det_succ_row_zero,Fin.sum_univ_succ,Matrix.submatrix,Fin.succAbove]

noncomputable def relationPolynomial : MvPolynomial (Fin 3) ℚ :=
  ExceptionalCriticalFamily.relation (X 0) (X 1) (X 2)

theorem relation_value : eval ![0,(-1:ℚ),1] relationPolynomial = 0 := by
  norm_num [relationPolynomial,ExceptionalCriticalFamily.relation]

theorem relation_partial_j :
    eval ![0,(-1:ℚ),1] (pderiv 2 relationPolynomial) = -2 := by
  norm_num [relationPolynomial,ExceptionalCriticalFamily.relation]
end ExceptionalSmoothJacobian
#print axioms ExceptionalSmoothJacobian.constraints_are_permanents
#print axioms ExceptionalSmoothJacobian.jacobian_formula
#print axioms ExceptionalSmoothJacobian.jacobian_determinant
#print axioms ExceptionalSmoothJacobian.relation_partial_j
