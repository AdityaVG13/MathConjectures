import PrimitiveFamily
import Mathlib.Tactic.NormNum

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ExceptionalSignSymmetries
variable {R : Type*} [CommRing R]
abbrev Mat (R : Type*) := Matrix (Fin 5) (Fin 5) R

def negateColumn (M : Mat R) (j : Fin 5) : Mat R :=
  M.updateCol j (fun r => -M r j)
def negateRow (M : Mat R) (i : Fin 5) : Mat R :=
  M.updateRow i (fun c => -M i c)
def actionA (M : Mat R) : Mat R :=
  negateColumn (M.submatrix (Equiv.swap 3 4) id) 4
def actionD (M : Mat R) : Mat R :=
  negateRow (M.submatrix id (Equiv.swap 0 2)) 1
def actionQ (M : Mat R) : Mat R :=
  negateColumn (M.submatrix (Equiv.swap 0 2) id) 1

theorem negateColumn_permanent (M : Mat R) (j : Fin 5) :
    (negateColumn M j).permanent = -M.permanent := by
  have hv : (-1:R) • (fun r => M r j) = (fun r => -M r j) := by
    funext r
    simp only [Pi.smul_apply,smul_eq_mul,neg_one_mul]
  have h := Matrix.permanent_updateCol_smul M j (-1:R) (fun r => M r j)
  rw [hv] at h
  simpa [negateColumn] using h
theorem negateRow_permanent (M : Mat R) (i : Fin 5) :
    (negateRow M i).permanent = -M.permanent := by
  have hv : (-1:R) • (fun c => M i c) = (fun c => -M i c) := by
    funext c
    simp only [Pi.smul_apply,smul_eq_mul,neg_one_mul]
  have h := Matrix.permanent_updateRow_smul M i (-1:R) (fun c => M i c)
  rw [hv] at h
  simpa [negateRow] using h

theorem actionA_permanent (M : Mat R) : (actionA M).permanent = -M.permanent := by
  rw [actionA,negateColumn_permanent,Matrix.permanent_permute_cols]
theorem actionD_permanent (M : Mat R) : (actionD M).permanent = -M.permanent := by
  rw [actionD,negateRow_permanent,Matrix.permanent_permute_rows]
theorem actionQ_permanent (M : Mat R) : (actionQ M).permanent = -M.permanent := by
  rw [actionQ,negateColumn_permanent,Matrix.permanent_permute_cols]

theorem actionA_involutive (M : Mat R) : actionA (actionA M) = M := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [actionA,negateColumn,Matrix.updateCol_apply,Matrix.submatrix,Equiv.swap_apply_def]
theorem actionD_involutive (M : Mat R) : actionD (actionD M) = M := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [actionD,negateRow,Matrix.updateRow_apply,Matrix.submatrix,Equiv.swap_apply_def]
theorem actionQ_involutive (M : Mat R) : actionQ (actionQ M) = M := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [actionQ,negateColumn,Matrix.updateCol_apply,Matrix.submatrix,Equiv.swap_apply_def]

theorem actions_commute (M : Mat R) :
    actionA (actionD M) = actionD (actionA M) ∧
    actionA (actionQ M) = actionQ (actionA M) ∧
    actionD (actionQ M) = actionQ (actionD M) := by
  repeat' constructor
  all_goals ext r c
  all_goals fin_cases r <;> fin_cases c <;>
    simp [actionA,actionD,actionQ,negateColumn,negateRow,Matrix.updateCol_apply,
      Matrix.updateRow_apply,Matrix.submatrix,Equiv.swap_apply_def]

theorem actions_fix_base :
    actionA (PrimitiveFamily.A (0:R)) = PrimitiveFamily.A 0 ∧
    actionD (PrimitiveFamily.A (0:R)) = PrimitiveFamily.A 0 ∧
    actionQ (PrimitiveFamily.A (0:R)) = PrimitiveFamily.A 0 := by
  repeat' constructor
  all_goals ext r c
  all_goals fin_cases r <;> fin_cases c <;>
    norm_num [actionA,actionD,actionQ,negateColumn,negateRow,Matrix.updateCol_apply,
      Matrix.updateRow_apply,Matrix.submatrix,Equiv.swap_apply_def,PrimitiveFamily.A]
end ExceptionalSignSymmetries
#print axioms ExceptionalSignSymmetries.actionA_permanent
#print axioms ExceptionalSignSymmetries.actionD_permanent
#print axioms ExceptionalSignSymmetries.actionQ_permanent
#print axioms ExceptionalSignSymmetries.actions_commute
#print axioms ExceptionalSignSymmetries.actions_fix_base
