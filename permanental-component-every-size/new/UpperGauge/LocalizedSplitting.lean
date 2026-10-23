import UpperGauge.VariableSplitting
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.MvPolynomial.Localization
namespace UniformUpperGauge
noncomputable section
open MvPolynomial
def polynomialQuotientAlgEquiv :
    (P ⧸ rawIdeal) ≃ₐ[ℂ] MvPolynomial (Fin 6) UniformNormalizedUpper.Quot :=
  (Ideal.quotientEquivAlg _ _ polynomialEquiv polynomialEquiv_ideal.symm).trans
    ((MvPolynomial.quotientEquivQuotientMvPolynomial _).symm.restrictScalars ℂ)

theorem normalizedIdeal_map_raw :
    cofactorIdeal normalized = Ideal.map (algebraMap P A) rawIdeal := by
  simp only [cofactorIdeal,rawIdeal,Ideal.map_span,←Set.range_comp]
  congr 2
  funext c
  simp only [Function.comp_apply,cofactor,rawCofactor,Matrix.permanent,map_sum,map_prod,Matrix.submatrix,
    Matrix.of_apply,id_eq]
  congr 1
  funext σ
  congr 1
  funext i
  by_cases hp : IsPivot (σ i,c.succAbove i) <;> simp [normalized,rawNormalized,matrix,hp]

abbrev D := P ⧸ rawIdeal
def qDelta : D := Ideal.Quotient.mk rawIdeal delta
abbrev LocalizedD := Localization.Away qDelta
abbrev NormalizedPivotQuot := A ⧸ cofactorIdeal normalized
abbrev MappedPivotQuot := A ⧸ rawIdeal.map (algebraMap P A)

instance mappedPivotQuot_localization : IsLocalization.Away qDelta MappedPivotQuot := by
  simpa [qDelta,Algebra.algebraMapSubmonoid,Submonoid.map_powers] using
    (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid D (Submonoid.powers delta)) MappedPivotQuot)

instance mappedPivotQuot_tower : IsScalarTower ℂ D MappedPivotQuot :=
  IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := D) (A := MappedPivotQuot) (by
    ext z
    rfl)

def normalizedPivotEquiv : NormalizedPivotQuot ≃ₐ[ℂ] LocalizedD :=
  (Ideal.quotientEquivAlgOfEq ℂ normalizedIdeal_map_raw).trans
    ((IsLocalization.algEquiv (Submonoid.powers qDelta) MappedPivotQuot LocalizedD).restrictScalars ℂ)

def splitDelta : MvPolynomial (Fin 6) UniformNormalizedUpper.Quot :=
  polynomialQuotientAlgEquiv qDelta
abbrev SplitLocalized := Localization.Away splitDelta

def localizedPolynomialEquiv : LocalizedD ≃ₐ[ℂ] SplitLocalized :=
  IsLocalization.algEquivOfAlgEquiv (M := Submonoid.powers qDelta)
    (T := Submonoid.powers splitDelta) LocalizedD SplitLocalized polynomialQuotientAlgEquiv
    (by rw [Submonoid.map_powers]; rfl)

def normalizedLaurentEquiv : NormalizedPivotQuot ≃ₐ[ℂ] SplitLocalized :=
  normalizedPivotEquiv.trans localizedPolynomialEquiv

#print axioms normalizedLaurentEquiv
end
end UniformUpperGauge
