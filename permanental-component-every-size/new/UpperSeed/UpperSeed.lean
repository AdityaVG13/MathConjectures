import Mathlib.Basic.Complex.Basic
import ExceptionalExpansion
import PrimitiveFamily
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace ComponentUpperSeed
noncomputable section

def B : Matrix (Fin 3) (Fin 4) ℂ :=
  !![1, 1, 1, 1;
     1, 7/9, -238/117, 2;
     1, -35/33, 7/78, 5/22]

def U : Matrix (Fin 3) (Fin 3) ℂ := B.submatrix id Fin.castSucc

def v : Fin 3 → ℂ := fun i => B i 3

def maximalPermanent (c : Fin 4) : ℂ :=
  (B.submatrix id c.succAbove).permanent

theorem maximal_permanents_zero : ∀ c : Fin 4, maximalPermanent c = 0 := by
  intro c
  fin_cases c
  all_goals unfold maximalPermanent
  all_goals rw [PrimitiveFamily.expand3]
  all_goals norm_num [Fin.sum_univ_succ, Fin.prod_univ_succ, PrimitiveFamily.enumerate3,
    PrimitiveFamily.q0, PrimitiveFamily.q1, PrimitiveFamily.q2, PrimitiveFamily.q3,
    PrimitiveFamily.q4, PrimitiveFamily.q5, Matrix.submatrix, Fin.succAbove, B]

theorem upper_det : U.det = -23359/3861 := by
  norm_num [U, B, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove]

theorem full_support : ∀ i j, B i j ≠ 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [B]

open MvPolynomial
abbrev P := MvPolynomial (Fin 3 × Fin 4) ℂ
noncomputable def genericB : Matrix (Fin 3) (Fin 4) P := fun i j => X (i,j)
def selected : Fin 4 → Fin 3 × Fin 4 := ![(0,0),(0,1),(0,2),(1,0)]
noncomputable def jac : Matrix (Fin 4) (Fin 4) ℂ := fun r c =>
  eval (fun ij => B ij.1 ij.2)
    (pderiv (selected c) ((genericB.submatrix id r.succAbove).permanent))

 theorem jac_det : jac.det = -1392580/382239 := by
  norm_num [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove]
  simp only [jac, PrimitiveFamily.expand3]
  norm_num [Fin.sum_univ_succ, Fin.prod_univ_succ, PrimitiveFamily.enumerate3,
    PrimitiveFamily.q0, PrimitiveFamily.q1, PrimitiveFamily.q2, PrimitiveFamily.q3,
    PrimitiveFamily.q4, PrimitiveFamily.q5, Matrix.submatrix, Fin.succAbove,
    genericB, selected, B]

theorem permanent_two (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M.permanent = M 0 0 * M 1 1 + M 1 0 * M 0 1 := by
  rw [ExceptionalExpansion.permanent_succ_column_zero]
  norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove]

def T : Matrix (Fin 3) (Fin 3) ℂ := fun c r =>
  (U.submatrix r.succAbove c.succAbove).permanent

def k : Fin 3 → ℂ := ![1034,994,1309]

def beta (u : Fin 3) : ℂ := ∑ r : Fin 3,
  U r u * ∏ s : Fin 2, v (r.succAbove s)

def eta : ℂ := k 0*k 1*beta 2 + k 0*k 2*beta 1 + k 1*k 2*beta 0

theorem right_kernel : T.mulVec v = 0 := by
  ext i
  fin_cases i <;>
    norm_num [T, permanent_two, U, B, v, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove]

theorem left_kernel : T.transpose.mulVec k = 0 := by
  ext i
  fin_cases i <;>
    norm_num [T, permanent_two, U, B, k, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Matrix.submatrix, Matrix.transpose_apply, Fin.succAbove]

theorem eta_value : eta = 1649340 := by
  norm_num [eta, beta, U, B, v, k, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Matrix.submatrix, Fin.succAbove]

theorem eta_ne_zero : eta ≠ 0 := by rw [eta_value]; norm_num

theorem kernel_vector (w : Fin 3 → ℂ) (hw : T.mulVec w = 0) :
    w = w 0 • v := by
  have h0 := congrFun hw 0
  have h1 := congrFun hw 1
  norm_num [T, permanent_two, U, B, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove] at h0 h1
  ext i
  fin_cases i
  · simp [v, B]
  · simp only [Pi.smul_apply, smul_eq_mul]
    norm_num [v, B]
    linear_combination (-363/833 : ℂ)*h0+(9/17 : ℂ)*h1
  · simp only [Pi.smul_apply, smul_eq_mul]
    norm_num [v, B]
    linear_combination (-45/98 : ℂ)*h0+(-9/22 : ℂ)*h1

theorem injective_on_first_zero (w : Fin 3 → ℂ) (hw0 : w 0 = 0)
    (hw : T.mulVec w = 0) : w = 0 := by
  rw [kernel_vector w hw, hw0, zero_smul]

theorem left_kernel_vector (w : Fin 3 → ℂ) (hw : T.transpose.mulVec w = 0) :
    w = (w 0 / 1034) • k := by
  have h0 := congrFun hw 0
  have h1 := congrFun hw 1
  norm_num [T, permanent_two, U, B, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.submatrix, Matrix.transpose_apply, Fin.succAbove] at h0 h1
  ext i
  fin_cases i
  · simp [k]
  · simp only [Pi.smul_apply, smul_eq_mul]
    norm_num [k]
    linear_combination (-234/1645 : ℂ)*h0+(156/235 : ℂ)*h1
  · simp only [Pi.smul_apply, smul_eq_mul]
    norm_num [k]
    linear_combination (-1683/658 : ℂ)*h0+(-429/94 : ℂ)*h1

#print axioms left_kernel_vector
#print axioms kernel_vector
#print axioms injective_on_first_zero
#print axioms right_kernel
#print axioms left_kernel
#print axioms eta_ne_zero
#print axioms jac_det
#print axioms maximal_permanents_zero
#print axioms upper_det
#print axioms full_support
end
end ComponentUpperSeed
