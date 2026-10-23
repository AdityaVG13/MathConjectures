import ExceptionalExpansion
import Mathlib.Tactic

set_option autoImplicit false
namespace ComponentLowerChart
open Matrix
variable {R : Type*} [CommRing R]

def entryUpdate {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) R)
    (a b : Fin (n+1)) (x : R) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  M.updateRow a (Function.update (M a) b x)

theorem entryUpdate_minor {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) R)
    (a b i : Fin (n+1)) (x : R) :
    (entryUpdate M a b x).submatrix i.succAbove b.succAbove =
      M.submatrix i.succAbove b.succAbove := by
  ext r c
  by_cases hr : i.succAbove r = a
  · simp [entryUpdate, Matrix.submatrix, Matrix.updateRow_apply, hr, Fin.succAbove_ne]
  · simp [entryUpdate, Matrix.submatrix, Matrix.updateRow_apply, hr]

theorem permanent_entryUpdate {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) R)
    (a b : Fin (n+1)) (x : R) :
    (entryUpdate M a b x).permanent = M.permanent +
      (x-M a b)*(M.submatrix a.succAbove b.succAbove).permanent := by
  rw [ExceptionalExpansion.permanent_expand_column _ b]
  simp_rw [entryUpdate_minor]
  have he (i : Fin (n+1)) : entryUpdate M a b x i b =
      M i b + if i = a then x-M a b else 0 := by
    by_cases hi : i = a
    · subst i; simp [entryUpdate, Matrix.updateRow_apply]
    · simp [entryUpdate, Matrix.updateRow_apply, hi]
  simp_rw [he, add_mul, Finset.sum_add_distrib]
  rw [← ExceptionalExpansion.permanent_expand_column M b]
  simp [ite_mul]

#print axioms permanent_entryUpdate
end ComponentLowerChart
