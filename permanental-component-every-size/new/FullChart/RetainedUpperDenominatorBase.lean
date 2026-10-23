import FullChart.RetainedUpperLocalization

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace UniformFullChart
noncomputable section
open MvPolynomial UniformUpperGauge UniformUpperQuadratic

@[simp] theorem map_upperDenom {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (d h : R) : f (denom d h) = denom (f d) (f h) := by
  simp [denom,rest,disc,normPlus,normMinus,alpha,beta,UniformUpperQuadratic.gamma,map_ofNat]

theorem normalizedPivotEquiv_mk (p : UniformUpperGauge.P) :
    normalizedPivotEquiv
      (Ideal.Quotient.mk (cofactorIdeal normalized) (algebraMap UniformUpperGauge.P A p)) =
      algebraMap D LocalizedD (Ideal.Quotient.mk rawIdeal p) := by
  simp only [normalizedPivotEquiv,AlgEquiv.trans_apply,Ideal.quotientEquivAlgOfEq_mk]
  change (IsLocalization.algEquiv (Submonoid.powers qDelta) MappedPivotQuot LocalizedD)
    (algebraMap D MappedPivotQuot (Ideal.Quotient.mk rawIdeal p)) = _
  exact (IsLocalization.algEquiv (Submonoid.powers qDelta) MappedPivotQuot LocalizedD).commutes _

theorem normalizedLaurentEquiv_mk (p : UniformUpperGauge.P) :
    normalizedLaurentEquiv
      (Ideal.Quotient.mk (cofactorIdeal normalized) (algebraMap UniformUpperGauge.P A p)) =
      algebraMap QPoly SplitLocalized
        (MvPolynomial.map (Ideal.Quotient.mk UniformNormalizedUpper.ideal) (polynomialEquiv p)) := by
  simp only [normalizedLaurentEquiv,AlgEquiv.trans_apply,normalizedPivotEquiv_mk,
    localizedPolynomialEquiv,IsLocalization.algEquivOfAlgEquiv_eq,polynomialQuotientAlgEquiv_mk]

theorem normalizedLaurentEquiv_interior (i : Fin 6) :
    normalizedLaurentEquiv
      (Ideal.Quotient.mk (cofactorIdeal normalized) (matrix (interior i).1 (interior i).2)) =
      algebraMap QPoly SplitLocalized
        (C (Ideal.Quotient.mk UniformNormalizedUpper.ideal (UniformNormalizedUpper.vars i))) := by
  simpa [matrix,UniformNormalizedUpper.vars] using normalizedLaurentEquiv_mk (X (interior i))

theorem normalizedLaurentEquiv_denom :
    normalizedLaurentEquiv
      (Ideal.Quotient.mk (cofactorIdeal normalized) (denom (matrix 1 3) (matrix 2 1))) =
      splitNormalDenom := by
  have h0 := normalizedLaurentEquiv_interior 0
  have h1 := normalizedLaurentEquiv_interior 1
  change normalizedLaurentEquiv (Ideal.Quotient.mk (cofactorIdeal normalized) (matrix 1 3)) = _ at h0
  change normalizedLaurentEquiv (Ideal.Quotient.mk (cofactorIdeal normalized) (matrix 2 1)) = _ at h1
  change (normalizedLaurentEquiv.toRingHom.comp (Ideal.Quotient.mk (cofactorIdeal normalized)))
    (denom (matrix 1 3) (matrix 2 1)) = _
  rw [map_upperDenom]
  change denom (normalizedLaurentEquiv (Ideal.Quotient.mk _ (matrix 1 3)))
    (normalizedLaurentEquiv (Ideal.Quotient.mk _ (matrix 2 1))) = _
  rw [h0,h1]
  simp only [splitNormalDenom,normalDenom,UniformNormalizedUpper.qDenom,map_upperDenom]
  exact (map_upperDenom ((algebraMap QPoly SplitLocalized).comp
    (C : UniformNormalizedUpper.Quot →+* QPoly)) _ _).symm

theorem actualQuotientAlgEquiv_mk (p : A) :
    actualQuotientAlgEquiv (Ideal.Quotient.mk (cofactorIdeal matrix) p) =
      Ideal.Quotient.mk (cofactorIdeal normalized) (inverseMap p) :=
  Ideal.quotientEquivAlg_mk _ coordinateAlgEquiv.symm map_cofactorIdeal.symm p


end
end UniformFullChart
#print axioms UniformFullChart.actualQuotientAlgEquiv_mk
