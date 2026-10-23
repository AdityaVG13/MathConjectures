import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace PrimitiveFamily
variable {R : Type*} [CommRing R]
def A (t : R) : Matrix (Fin 5) (Fin 5) R :=
  !![1, 1, 1, 1, 0;
     1, 0, -1, 0, 0;
     1, -1, 1, 1, 0;
     t, 0, t, 1, 1;
     t, 0, t, 1, -1]

def p0 : Equiv.Perm (Fin 4) := ⟨![0, 1, 2, 3], ![0, 1, 2, 3], by decide, by decide⟩
def p1 : Equiv.Perm (Fin 4) := ⟨![0, 1, 3, 2], ![0, 1, 3, 2], by decide, by decide⟩
def p2 : Equiv.Perm (Fin 4) := ⟨![0, 2, 1, 3], ![0, 2, 1, 3], by decide, by decide⟩
def p3 : Equiv.Perm (Fin 4) := ⟨![0, 2, 3, 1], ![0, 3, 1, 2], by decide, by decide⟩
def p4 : Equiv.Perm (Fin 4) := ⟨![0, 3, 1, 2], ![0, 2, 3, 1], by decide, by decide⟩
def p5 : Equiv.Perm (Fin 4) := ⟨![0, 3, 2, 1], ![0, 3, 2, 1], by decide, by decide⟩
def p6 : Equiv.Perm (Fin 4) := ⟨![1, 0, 2, 3], ![1, 0, 2, 3], by decide, by decide⟩
def p7 : Equiv.Perm (Fin 4) := ⟨![1, 0, 3, 2], ![1, 0, 3, 2], by decide, by decide⟩
def p8 : Equiv.Perm (Fin 4) := ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩
def p9 : Equiv.Perm (Fin 4) := ⟨![1, 2, 3, 0], ![3, 0, 1, 2], by decide, by decide⟩
def p10 : Equiv.Perm (Fin 4) := ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩
def p11 : Equiv.Perm (Fin 4) := ⟨![1, 3, 2, 0], ![3, 0, 2, 1], by decide, by decide⟩
def p12 : Equiv.Perm (Fin 4) := ⟨![2, 0, 1, 3], ![1, 2, 0, 3], by decide, by decide⟩
def p13 : Equiv.Perm (Fin 4) := ⟨![2, 0, 3, 1], ![1, 3, 0, 2], by decide, by decide⟩
def p14 : Equiv.Perm (Fin 4) := ⟨![2, 1, 0, 3], ![2, 1, 0, 3], by decide, by decide⟩
def p15 : Equiv.Perm (Fin 4) := ⟨![2, 1, 3, 0], ![3, 1, 0, 2], by decide, by decide⟩
def p16 : Equiv.Perm (Fin 4) := ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩
def p17 : Equiv.Perm (Fin 4) := ⟨![2, 3, 1, 0], ![3, 2, 0, 1], by decide, by decide⟩
def p18 : Equiv.Perm (Fin 4) := ⟨![3, 0, 1, 2], ![1, 2, 3, 0], by decide, by decide⟩
def p19 : Equiv.Perm (Fin 4) := ⟨![3, 0, 2, 1], ![1, 3, 2, 0], by decide, by decide⟩
def p20 : Equiv.Perm (Fin 4) := ⟨![3, 1, 0, 2], ![2, 1, 3, 0], by decide, by decide⟩
def p21 : Equiv.Perm (Fin 4) := ⟨![3, 1, 2, 0], ![3, 1, 2, 0], by decide, by decide⟩
def p22 : Equiv.Perm (Fin 4) := ⟨![3, 2, 0, 1], ![2, 3, 1, 0], by decide, by decide⟩
def p23 : Equiv.Perm (Fin 4) := ⟨![3, 2, 1, 0], ![3, 2, 1, 0], by decide, by decide⟩
noncomputable def enumerate4 : Fin 24 ≃ Equiv.Perm (Fin 4) :=
  Equiv.ofBijective ![p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23] (by decide +kernel)
theorem expand4 (M : Matrix (Fin 4) (Fin 4) R) :
    M.permanent = ∑ k : Fin 24, ∏ j, M (enumerate4 k j) j := by
  exact (Equiv.sum_comp enumerate4 (fun p => ∏ j, M (p j) j)).symm

theorem permanent_four (t : R) :
    ∀ r c : Fin 5, ((A t).submatrix r.succAbove c.succAbove).permanent = 0 := by
  intro r c
  fin_cases r <;> fin_cases c
  all_goals rw [expand4]
  all_goals simp [Fin.sum_univ_succ, Fin.prod_univ_succ, enumerate4,
    p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23,
    Matrix.submatrix, A, Fin.succAbove]
  all_goals ring
theorem determinant (t : R) : (A t).det = 8 * (1 - t) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix, A, Fin.succAbove]
  ring



def q0 : Equiv.Perm (Fin 3) := ⟨![0, 1, 2], ![0, 1, 2], by decide, by decide⟩
def q1 : Equiv.Perm (Fin 3) := ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩
def q2 : Equiv.Perm (Fin 3) := ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩
def q3 : Equiv.Perm (Fin 3) := ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩
def q4 : Equiv.Perm (Fin 3) := ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩
def q5 : Equiv.Perm (Fin 3) := ⟨![2, 1, 0], ![2, 1, 0], by decide, by decide⟩
noncomputable def enumerate3 : Fin 6 ≃ Equiv.Perm (Fin 3) :=
  Equiv.ofBijective ![q0, q1, q2, q3, q4, q5] (by decide +kernel)
theorem expand3 (M : Matrix (Fin 3) (Fin 3) R) :
    M.permanent = ∑ k : Fin 6, ∏ j, M (enumerate3 k j) j := by
  exact (Equiv.sum_comp enumerate3 (fun p => ∏ j, M (p j) j)).symm

theorem permanent_three (t : R) :
    ((A t).submatrix ![0, 1, 3] ![1, 2, 4]).permanent = -1 := by
  rw [expand3]
  simp [Fin.sum_univ_succ, Fin.prod_univ_succ, enumerate3,
    q0, q1, q2, q3, q4, q5, Matrix.submatrix, A]

#print axioms permanent_three
#print axioms determinant
#print axioms permanent_four
end PrimitiveFamily
