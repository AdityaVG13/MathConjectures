import ParametricEntryJetLemmas
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Actual derivatives of the twelve stationary cofactor equations at s=0.
This is a semantic coefficient certificate, not only an inverse of a copied table.
The separate cofactor-gradient rule identifies this with the potential Hessian;
that formal derivative bridge is not asserted in this module. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace ExceptionalStationaryJacobian
open ConcreteLocalGeometry ParametricLocalGeometry PrimitiveFamily

def principalPairs : Fin 12 → Fin 5 × Fin 5 :=
  ![(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1),(4,2),(4,4)]
noncomputable def firstVector (f : P) : Fin 12 → ℂ :=
  ![firstDerivative 4 f,firstDerivative 5 f,firstDerivative 6 f,
    firstDerivative 7 f,firstDerivative 8 f,firstDerivative 9 f,
    firstDerivative 10 f,firstDerivative 11 f,firstDerivative 12 f,
    firstDerivative 13 f,firstDerivative 14 f,firstDerivative 15 f]
noncomputable def stationaryJacobian : Matrix (Fin 12) (Fin 12) ℂ :=
  fun i => firstVector (translatedEquation 0 (principalPairs i))

def coefficientTable : Matrix (Fin 12) (Fin 12) ℂ :=
  !![0,0,0,0,0,0,-2,0,-2,0,2,2;
    0,0,0,0,0,0,0,-2,0,2,0,0;
    0,0,0,0,0,0,0,2,0,2,0,0;
    0,0,0,0,0,0,0,-1,0,1,0,1;
    0,0,0,0,0,0,1,0,-1,0,1,0;
    0,0,0,0,0,0,-1,0,1,0,1,0;
    -2,0,0,0,1,-1,0,0,0,0,0,0;
    0,-2,2,-1,0,0,0,0,0,0,0,0;
    -2,0,0,0,-1,1,0,0,0,0,0,0;
    0,2,2,1,0,0,0,0,0,0,0,0;
    2,0,0,0,1,1,0,0,0,0,0,0;
    2,0,0,1,0,0,0,0,0,0,0,0]

def scaledInverse : Matrix (Fin 12) (Fin 12) ℂ :=
  !![0,0,0,0,0,0,-1,0,-1,0,0,0;
    0,0,0,0,0,0,-1,-1,-1,1,0,-2;
    0,0,0,0,0,0,0,1,0,1,0,0;
    0,0,0,0,0,0,2,0,2,0,0,4;
    0,0,0,0,0,0,2,0,0,0,2,0;
    0,0,0,0,0,0,0,0,2,0,2,0;
    -1,-1,0,2,2,0,0,0,0,0,0,0;
    0,-1,1,0,0,0,0,0,0,0,0,0;
    -1,-1,0,2,0,2,0,0,0,0,0,0;
    0,1,1,0,0,0,0,0,0,0,0,0;
    0,0,0,0,2,2,0,0,0,0,0,0;
    0,-2,0,4,0,0,0,0,0,0,0,0]

theorem actual_vector (i : Fin 12) : stationaryJacobian i = coefficientTable i := by
  fin_cases i
  all_goals simp only [stationaryJacobian,firstVector,principalPairs,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  all_goals unfold translatedEquation
  all_goals simp only [expand4]
  all_goals norm_num [Fin.sum_univ_succ,Fin.prod_univ_succ,enumerate4,
    p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,
    Matrix.submatrix,Fin.succAbove,parametricEntryJetTable,jetFirstSlot,coefficientTable]
  all_goals repeat' constructor
  all_goals ring

theorem actual_matrix : stationaryJacobian = coefficientTable := by
  ext i j
  exact congrFun (actual_vector i) j

theorem scaled_inverse : scaledInverse * coefficientTable =
    (4:ℂ) • (1:Matrix (Fin 12) (Fin 12) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply,Fin.sum_univ_succ,scaledInverse,coefficientTable,
      Matrix.smul_apply,Matrix.one_apply]

theorem actual_inverse : ((4:ℂ)⁻¹ • scaledInverse) * stationaryJacobian = 1 := by
  rw [actual_matrix,Matrix.smul_mul,scaled_inverse,smul_smul]
  norm_num

theorem actual_rank : stationaryJacobian.rank = 12 := by
  apply le_antisymm stationaryJacobian.rank_le_width
  have h := Matrix.rank_mul_le_right ((4:ℂ)⁻¹ • scaledInverse) stationaryJacobian
  simpa only [actual_inverse,Matrix.rank_one,Fintype.card_fin] using h
end ExceptionalStationaryJacobian
#print axioms ExceptionalStationaryJacobian.actual_vector
#print axioms ExceptionalStationaryJacobian.actual_inverse
#print axioms ExceptionalStationaryJacobian.actual_rank
