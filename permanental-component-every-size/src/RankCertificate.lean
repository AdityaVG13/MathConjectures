import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace LocalGeometryRank

/-- The 25 by 15 rational coefficient table printed by experiment 033.
    Column order: e4,...,e15, a*d, a*q, d*q.
    Row order: deleting (i,j), lexicographically, from the 5 by 5 slice.
    This definition imports data, not a proof of its polynomial provenance. -/
def coefficientMatrix : Matrix (Fin 25) (Fin 15) ℚ :=
  !![0, 0, -100, 0, 0, 0, 0, 25, 0, -25, 0, 25, 200, 20, 0;
     0, 0, 400, 0, 0, 0, 25, 0, -25, 0, 25, 0, -200, 0, 0;
     0, 0, -100, 0, 0, 0, 0, -25, 0, 25, 0, -25, 200, -20, 0;
     0, 0, -200, 0, 0, 0, -25, 0, 25, 0, -25, 0, -200, 0, 0;
     400, -100, 0, 0, 0, 0, 25, 0, -25, 0, -25, 0, -600, 0, 20;
     0, 0, 0, 0, 0, 100, 0, -50, 0, 50, 0, 0, 0, -20, 0;
     0, 0, 0, 0, 0, 400, -50, 0, -50, 0, 50, 250, -600, 200, 0;
     0, 0, 0, 0, 0, 100, 0, -50, 0, 50, 0, 0, 0, -20, 0;
     0, 0, 0, 0, 0, 200, 0, -50, 0, 50, 0, 0, 0, -360, 0;
     0, 0, 0, 100, 200, 0, 0, 250, 0, 250, 0, 0, 0, 80, -20;
     0, 0, 100, 0, 0, 0, 0, 25, 0, -25, 0, -25, -200, 20, 0;
     0, 0, 400, 0, 0, 0, 25, 0, -25, 0, 25, 0, -200, 0, 0;
     0, 0, 100, 0, 0, 0, 0, -25, 0, 25, 0, 25, -200, -20, 0;
     0, 0, 200, 0, 0, 0, 25, 0, -25, 0, 25, 0, 200, 0, 0;
     400, 100, 0, 0, 0, 0, -25, 0, 25, 0, 25, 0, 600, 0, 20;
     -10, 0, 0, 0, 5, -5, 0, 0, 0, 0, 0, 0, 0, -1, -5;
     0, -10, 50, -5, 0, 0, 0, 0, 0, 0, 0, 0, -10, 0, -5;
     -10, 0, 0, 0, -5, 5, 0, 0, 0, 0, 0, 0, 0, 1, -5;
     -10, 0, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5;
     50, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15;
     10, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, 0, -1, 5;
     0, 10, 50, 5, 0, 0, 0, 0, 0, 0, 0, 0, -10, 0, 5;
     10, 0, 0, 0, 5, 5, 0, 0, 0, 0, 0, 0, 0, 1, 5;
     10, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5;
     50, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15]

/-- Zero-based row indices printed by experiment 034. -/
def selectedRows : Fin 15 → Fin 25 :=
  ![0, 1, 2, 4, 5, 6, 8, 9, 10, 14, 15, 16, 17, 18, 21]

def selectedMatrix : Matrix (Fin 15) (Fin 15) ℚ :=
  coefficientMatrix.submatrix selectedRows id

/-- Exact rational inverse printed by experiment 034. -/
def inverseMatrix : Matrix (Fin 15) (Fin 15) ℚ :=
  !![0, 0, 0, 1/720, 0, 0, 0, 0, 0, 1/720, 1/180, 0, 1/180, 0, 0;
     0, 0, 0, 1/240, 0, 0, 0, 0, 0, 1/240, 7/60, -1/20, 7/60, 1/10, 1/20;
     1/1800, 0, 1/1800, 0, 0, 0, 0, 0, 0, 0, 0, 1/90, 0, 0, 1/90;
     0, 0, 0, -1/180, 0, 0, 0, 0, 0, -1/180, -11/90, 0, -11/90, -1/5, 0;
     1/100, 0, 0, 0, 1/100, 0, 0, 0, 1/100, 0, 1/10, 0, -1/10, 0, 0;
     17/1800, 0, 0, 0, 2/225, 0, 1/1800, 0, 17/1800, 0, 0, 0, 0, 0, 0;
     1/30, 1/50, -3/50, 0, 7/150, -1/100, -1/300, 0, -1/150, 0, 0, -1/10, 0, 0, -1/10;
     1/225, 0, 0, 1/1000, -8/1125, 0, 7/4500, 1/500, 1/225, 1/1000, -1/50, 0, 3/50, 1/25, 0;
     -1/150, 0, -1/10, -11/600, 7/150, -1/100, -1/300, 0, -1/150, 1/600, -7/30, 0, -7/30, -1/5, -1/5;
     -1/75, 0, 0, 1/1000, -1/375, 0, -1/1500, 1/500, -1/75, 1/1000, -1/50, 0, 3/50, 1/25, 0;
     -2/75, 1/50, -2/75, -11/600, 0, 0, 0, 0, 0, 1/600, -7/30, -1/30, -7/30, -1/5, -7/30;
     0, 0, -1/50, 0, 0, 0, 0, 0, -1/50, 0, 0, 0, 0, 0, 0;
     1/360, 0, 1/360, 0, 0, 0, 0, 0, 0, 0, 0, 1/180, 0, 0, 1/180;
     1/360, 0, 0, 0, 1/180, 0, -1/360, 0, 1/360, 0, 0, 0, 0, 0, 0;
     0, 0, 0, -1/360, 0, 0, 0, 0, 0, -1/360, -1/9, 0, -1/9, 0, 0]

/-- Exact equality, checked with rational normalization in the Lean kernel. -/
theorem inverse_mul_selected : inverseMatrix * selectedMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num [Matrix.mul_apply, Fin.sum_univ_succ, inverseMatrix,
    selectedMatrix, coefficientMatrix, selectedRows, Matrix.submatrix, Matrix.one_apply]

#print axioms inverse_mul_selected
end LocalGeometryRank
