import UpperGauge.NormalizedBridge
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Polynomial.Quotient
namespace UniformUpperGauge
noncomputable section
open MvPolynomial
def gaugeIndex : Fin 6 → Index := ![(0,0),(0,1),(0,2),(0,3),(1,0),(2,0)]
def splitIndex : Index → Fin 6 ⊕ Fin 6 := fun ij =>
  (![![Sum.inl 0,Sum.inl 1,Sum.inl 2,Sum.inl 3],
     ![Sum.inl 4,Sum.inr 2,Sum.inr 3,Sum.inr 0],
     ![Sum.inl 5,Sum.inr 1,Sum.inr 4,Sum.inr 5]] : Fin 3 → Fin 4 → Fin 6 ⊕ Fin 6) ij.1 ij.2
def indexEquiv : Index ≃ Fin 6 ⊕ Fin 6 where
  toFun := splitIndex
  invFun := Sum.elim gaugeIndex interior
  left_inv := by rintro ⟨i,j⟩; fin_cases i <;> fin_cases j <;> rfl
  right_inv := by intro s; cases s with
    | inl i => fin_cases i <;> rfl
    | inr i => fin_cases i <;> rfl
abbrev Split := MvPolynomial (Fin 6) UniformNormalizedUpper.Coordinates
def polynomialEquiv : P ≃ₐ[ℂ] Split :=
  (MvPolynomial.renameEquiv ℂ indexEquiv).trans (MvPolynomial.sumAlgEquiv ℂ (Fin 6) (Fin 6))
@[simp] theorem polynomialEquiv_gauge (s : Fin 6) :
    polynomialEquiv (X (gaugeIndex s)) = X s := by
  fin_cases s <;> simp [polynomialEquiv,MvPolynomial.renameEquiv, indexEquiv,splitIndex,gaugeIndex]
@[simp] theorem polynomialEquiv_interior (s : Fin 6) :
    polynomialEquiv (X (interior s)) = C (X s) := by
  fin_cases s <;> simp [polynomialEquiv,MvPolynomial.renameEquiv,indexEquiv,splitIndex,interior]
def rawNormalized : Matrix (Fin 3) (Fin 4) P := fun i j =>
  if IsPivot (i,j) then 1 else X (i,j)
def rawCofactor (c : Fin 4) : P := (rawNormalized.submatrix id c.succAbove).permanent
def rawIdeal : Ideal P := Ideal.span (Set.range rawCofactor)

theorem polynomialEquiv_normalized (i : Fin 3) (j : Fin 4) :
    polynomialEquiv (rawNormalized i j) =
      C (UniformNormalizedUpper.normalizedMatrix i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [rawNormalized,IsPivot,UniformNormalizedUpper.normalizedMatrix,
      UniformNormalizedUpper.vars,polynomialEquiv,MvPolynomial.renameEquiv,
      indexEquiv,splitIndex]
theorem polynomialEquiv_cofactor (c : Fin 4) :
    polynomialEquiv (rawCofactor c) = C (UniformNormalizedUpper.actualCofactor c) := by
  simp only [rawCofactor,UniformNormalizedUpper.actualCofactor,Matrix.permanent,
    map_sum,map_prod,Matrix.submatrix,Matrix.of_apply,id_eq,polynomialEquiv_normalized]

theorem polynomialEquiv_ideal :
    Ideal.map polynomialEquiv.toRingHom rawIdeal =
      Ideal.map (C : UniformNormalizedUpper.Coordinates →+* Split) UniformNormalizedUpper.ideal := by
  rw [UniformNormalizedUpper.ideal_eq_actualCofactors]
  simp only [rawIdeal,Ideal.map_span,←Set.range_comp]
  congr 2
  funext c
  exact polynomialEquiv_cofactor c

def polynomialQuotientEquiv : (P ⧸ rawIdeal) ≃+* MvPolynomial (Fin 6) UniformNormalizedUpper.Quot :=
  (Ideal.quotientEquiv _ _ polynomialEquiv.toRingEquiv polynomialEquiv_ideal.symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial _).symm.toRingEquiv
#print axioms polynomialQuotientEquiv
end
end UniformUpperGauge
