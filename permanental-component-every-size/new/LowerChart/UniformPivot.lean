import LowerChart.EntryUpdate
import LowerChart.LinearRoot
import SparseSeed.DeletionBridge
import FamilyContainment.IdealContainment
import DimensionClosure.FiniteTypeDimension
import Mathlib.RingTheory.Localization.Away.Basic

set_option autoImplicit false
namespace ComponentLowerChart
noncomputable section
open Matrix

abbrev LowerIndex (k : ℕ) := Fin (k+1) × Fin (k+1)
abbrev FreeLower (k : ℕ) := {ij : LowerIndex k // ij ≠ (0,0)}
abbrev LowerParameters (k : ℕ) := MvPolynomial (FreeLower k) ℂ

def zeroHub (k : ℕ) : Matrix (Fin (k+1)) (Fin (k+1)) (LowerParameters k) :=
  fun i j => if h : (i,j) = (0,0) then 0 else MvPolynomial.X ⟨(i,j),h⟩

def pivotCoefficient (k : ℕ) : LowerParameters k :=
  ((zeroHub k).submatrix (0 : Fin (k+1)).succAbove (0 : Fin (k+1)).succAbove).permanent

def pivotConstant (k : ℕ) : LowerParameters k := (zeroHub k).permanent

def polynomialMatrix (k : ℕ) :
    Matrix (Fin (k+1)) (Fin (k+1)) (Polynomial (LowerParameters k)) :=
  entryUpdate ((zeroHub k).map Polynomial.C) 0 0 Polynomial.X

theorem permanent_polynomialMatrix (k : ℕ) :
    (polynomialMatrix k).permanent =
      Polynomial.C (pivotCoefficient k)*Polynomial.X + Polynomial.C (pivotConstant k) := by
  rw [polynomialMatrix, permanent_entryUpdate]
  have hm : ((zeroHub k).map Polynomial.C).permanent = Polynomial.C (pivotConstant k) :=
    ComponentFamilyContainment.permanent_map Polynomial.C (zeroHub k)
  have hc : (((zeroHub k).map Polynomial.C).submatrix
      (0 : Fin (k+1)).succAbove (0 : Fin (k+1)).succAbove).permanent =
      Polynomial.C (pivotCoefficient k) :=
    ComponentFamilyContainment.permanent_map Polynomial.C
      ((zeroHub k).submatrix (0 : Fin (k+1)).succAbove (0 : Fin (k+1)).succAbove)
  rw [hm, hc]
  have hz : zeroHub k 0 0 = 0 := by simp [zeroHub]
  simp only [Matrix.map_apply, hz, map_zero, sub_zero]
  ring

def lowerSeed (k : ℕ) : FreeLower k → ℂ :=
  fun ij => SparseSeed.finArrowhead k ij.val.1 ij.val.2

theorem pivotCoefficient_seed (k : ℕ) : MvPolynomial.eval (lowerSeed k) (pivotCoefficient k) = 1 := by
  unfold pivotCoefficient
  rw [← ComponentFamilyContainment.permanent_map (MvPolynomial.eval (lowerSeed k))]
  have hm : (((zeroHub k).submatrix (0 : Fin (k+1)).succAbove
      (0 : Fin (k+1)).succAbove).map (MvPolynomial.eval (lowerSeed k))) =
      (1 : Matrix (Fin k) (Fin k) ℂ) := by
    ext i j
    simp [zeroHub, Matrix.map_apply, Matrix.submatrix, lowerSeed,
      SparseSeed.finArrowhead, SparseSeed.arrowhead, Matrix.one_apply]
  rw [hm, Matrix.permanent_one]

theorem pivotCoefficient_ne_zero (k : ℕ) : pivotCoefficient k ≠ 0 := by
  intro h
  have he := pivotCoefficient_seed k
  rw [h, map_zero] at he
  exact zero_ne_one he

abbrev LowerBase (k : ℕ) := Localization.Away (pivotCoefficient k)
instance (k : ℕ) : IsDomain (LowerBase k) :=
  Localization.Away.isDomain (pivotCoefficient_ne_zero k)

def pivotUnit (k : ℕ) : (LowerBase k)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := LowerBase k) (pivotCoefficient k)).unit

def lowerEquation (k : ℕ) : Polynomial (LowerBase k) :=
  linearPolynomial (pivotUnit k) (algebraMap (LowerParameters k) (LowerBase k) (pivotConstant k))
abbrev LowerRootChart (k : ℕ) := AdjoinRoot (lowerEquation k)

def lowerChartEquiv (k : ℕ) : LowerRootChart k ≃ₐ[LowerBase k] LowerBase k :=
  linearRootEquiv (pivotUnit k) _

#print axioms permanent_polynomialMatrix
#print axioms pivotCoefficient_seed
#print axioms lowerChartEquiv
end
end ComponentLowerChart
