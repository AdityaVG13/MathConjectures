import PrimitiveFamily
import Mathlib.Tactic.NormNum

/-! Exact polynomial certificate from emath058. This proves the critical-family
identities, not the formal Morse normal form or its historical novelty. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ExceptionalCriticalFamily
variable {R : Type*} [CommRing R]

def denominator (d j : R) : R := (j+1)*(j-d)
def eNumerator (d h j : R) : R := -((d+1)*h+d+j)
def fNumerator (d h j : R) : R :=
  (d-1)*(j+d)*(j+1)-eNumerator d h j*(j-d)
def iNumerator (d h j : R) : R :=
  -(j-1)*(j+d)*(j+1)-h*denominator d j
def relation (d h j : R) : R :=
  (d+1)*h*(j+d)*(j-1)+(d+1)*h*h*(j-d)+(d-1)*j*(j+d)
def matrix (d h j a : R) : Matrix (Fin 5) (Fin 5) R :=
  !![1,1,1,1,a;
     denominator d j,eNumerator d h j*(j-d),fNumerator d h j,
       denominator d j*d,denominator d j*d*a;
     denominator d j,denominator d j*h,iNumerator d h j,
       denominator d j*j,denominator d j*j*a;
     0,0,0,1,1;
     0,0,0,1,-1]
def multipliers (a : R) : Matrix (Fin 5) (Fin 5) R :=
  !![0,0,0,0,0;0,0,0,0,0;0,0,0,0,0;
     a-1,0,0,-1,1;a+1,0,0,1,1]

theorem cofactor_formula (d h j a : R) : ∀ r c : Fin 5,
    ((matrix d h j a).submatrix r.succAbove c.succAbove).permanent =
      2*denominator d j*relation d h j*multipliers a r c := by
  intro r c
  fin_cases r <;> fin_cases c
  all_goals rw [PrimitiveFamily.expand4]
  all_goals norm_num [Fin.sum_univ_succ,Fin.prod_univ_succ,PrimitiveFamily.enumerate4,
    PrimitiveFamily.p0,PrimitiveFamily.p1,PrimitiveFamily.p2,PrimitiveFamily.p3,
    PrimitiveFamily.p4,PrimitiveFamily.p5,PrimitiveFamily.p6,PrimitiveFamily.p7,
    PrimitiveFamily.p8,PrimitiveFamily.p9,PrimitiveFamily.p10,PrimitiveFamily.p11,
    PrimitiveFamily.p12,PrimitiveFamily.p13,PrimitiveFamily.p14,PrimitiveFamily.p15,
    PrimitiveFamily.p16,PrimitiveFamily.p17,PrimitiveFamily.p18,PrimitiveFamily.p19,
    PrimitiveFamily.p20,PrimitiveFamily.p21,PrimitiveFamily.p22,PrimitiveFamily.p23,
    Matrix.submatrix,Fin.succAbove,matrix,multipliers,denominator,
    eNumerator,fNumerator,iNumerator,relation]
  all_goals ring

theorem zero_relation_critical (d h j a : R) (hr : relation d h j = 0) :
    ∀ r c : Fin 5,
      ((matrix d h j a).submatrix r.succAbove c.succAbove).permanent = 0 := by
  intro r c
  rw [cofactor_formula,hr]
  ring

theorem cleared_basepoint :
    matrix (0:R) (-1) 1 0 =
      fun r c => (![1,2,2,1,1] r : R)*PrimitiveFamily.A (0:R) r c := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    norm_num [matrix,denominator,eNumerator,fNumerator,iNumerator,PrimitiveFamily.A]
end ExceptionalCriticalFamily
#print axioms ExceptionalCriticalFamily.cofactor_formula
#print axioms ExceptionalCriticalFamily.zero_relation_critical
#print axioms ExceptionalCriticalFamily.cleared_basepoint
