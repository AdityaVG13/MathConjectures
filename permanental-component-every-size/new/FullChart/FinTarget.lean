import FullChart.PolynomialTarget
namespace UniformFullChartTarget
noncomputable section
open MvPolynomial TensorProduct
def freeCount (k : ℕ) : ℕ := (k+1)^2+(k+1)+4
def finalIndexEquiv (k : ℕ) : FinalIndex k ≃ Fin (freeCount k) :=
  Fintype.equivFinOfCardEq (finalIndex_card k)
abbrev FinPoly (k : ℕ) := MvPolynomial (Fin (freeCount k)) UniformUpperQuadratic.Chart
def finPolynomialEquiv (k : ℕ) : FinalPoly k ≃ₐ[ℂ] FinPoly k :=
  (MvPolynomial.renameEquiv UniformUpperQuadratic.Chart (finalIndexEquiv k)).restrictScalars ℂ
def finDenom (k : ℕ) : FinPoly k := finPolynomialEquiv k (finalDenom k)
abbrev FinChart (k : ℕ) := Localization.Away (finDenom k)
def finChartEquiv (k : ℕ) : FinalChart k ≃ₐ[ℂ] FinChart k :=
  IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers (finalDenom k)) (T := Submonoid.powers (finDenom k))
    _ _ (finPolynomialEquiv k) (by rw [Submonoid.map_powers]; rfl)
def fullFinTargetEquiv (k : ℕ) :
    MvPolynomial (Fin k) (UT ⊗[ℂ] ComponentLowerChart.LowerBase k) ≃ₐ[ℂ] FinChart k :=
  (fullTargetEquiv k).trans (finChartEquiv k)
#print axioms fullFinTargetEquiv
end
end UniformFullChartTarget
