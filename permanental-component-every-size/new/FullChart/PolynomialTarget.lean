import FullChart.FactorTarget
set_option backward.isDefEq.respectTransparency false
namespace UniformFullChartTarget
noncomputable section
open MvPolynomial TensorProduct
open UniformUpperGauge ComponentLowerChart
abbrev ExtendedRaw (k : ℕ) := MvPolynomial (Fin k) (RawPoly k)
abbrev Extended (k : ℕ) := MvPolynomial (Fin k) (CombinedLocalized k)
def extendedFactor (k : ℕ) : ExtendedRaw k := C (combinedFactor k)
attribute [local instance] MvPolynomial.algebraMvPolynomial
instance extendedLocalization (k : ℕ) : IsLocalization.Away (extendedFactor k) (Extended k) := by
  simpa only [extendedFactor,Submonoid.map_powers] using
    (inferInstance : IsLocalization ((Submonoid.powers (combinedFactor k)).map
      (C : RawPoly k →+* ExtendedRaw k)) (Extended k))
instance extendedScalarTower (k : ℕ) : IsScalarTower ℂ (ExtendedRaw k) (Extended k) :=
  IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := ExtendedRaw k) (A := Extended k) (by
    apply RingHom.ext
    intro z
    change C (algebraMap ℂ (CombinedLocalized k) z) =
      MvPolynomial.map (algebraMap (RawPoly k) (CombinedLocalized k))
        (C (algebraMap ℂ (RawPoly k) z))
    rw [MvPolynomial.map_C,IsScalarTower.algebraMap_apply ℂ (RawPoly k) (CombinedLocalized k)])

abbrev FinalIndex (k : ℕ) := Fin k ⊕ (FreeLower k ⊕ Fin 6)
abbrev FinalPoly (k : ℕ) := MvPolynomial (FinalIndex k) UniformUpperQuadratic.Chart
def flattenEquiv (k : ℕ) : ExtendedRaw k ≃ₐ[ℂ] FinalPoly k :=
  ((MvPolynomial.mapAlgEquiv (Fin k)
    ((MvPolynomial.sumAlgEquiv UniformUpperQuadratic.Chart (FreeLower k) (Fin 6)).symm.restrictScalars ℂ)).trans
    ((MvPolynomial.sumAlgEquiv UniformUpperQuadratic.Chart (Fin k) (FreeLower k ⊕ Fin 6)).symm.restrictScalars ℂ))
def finalDenom (k : ℕ) : FinalPoly k := flattenEquiv k (extendedFactor k)
abbrev FinalChart (k : ℕ) := Localization.Away (finalDenom k)
def extendedFinalEquiv (k : ℕ) : Extended k ≃ₐ[ℂ] FinalChart k :=
  IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers (extendedFactor k)) (T := Submonoid.powers (finalDenom k))
    _ _ (flattenEquiv k) (by rw [Submonoid.map_powers]; rfl)
def fullTargetEquiv (k : ℕ) :
    MvPolynomial (Fin k) (UT ⊗[ℂ] LowerBase k) ≃ₐ[ℂ] FinalChart k :=
  (MvPolynomial.mapAlgEquiv (Fin k) (upperLowerTargetEquiv k)).trans (extendedFinalEquiv k)

theorem finalIndex_card (k : ℕ) :
    Fintype.card (FinalIndex k) = (k+1)^2 + (k+1) + 4 := by
  have hc : Fintype.card (FreeLower k) = (k+1)^2 - 1 := by
    simpa [FreeLower,LowerIndex,Fintype.card_prod,pow_two] using
      Fintype.card_subtype_compl (fun ij : LowerIndex k => ij = (0,0))
  simp only [FinalIndex,Fintype.card_sum,Fintype.card_fin,hc]
  have h : 0 < (k+1)^2 := by positivity
  omega

#print axioms fullTargetEquiv
#print axioms finalIndex_card
end
end UniformFullChartTarget
