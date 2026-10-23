import FullChart.RetainedUpperDenominatorBase

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace UniformFullChart
noncomputable section
open MvPolynomial UniformUpperGauge UniformUpperQuadratic

theorem actualLaurentEquiv_symm_apply (q : SplitLocalized) :
    actualLaurentEquiv.symm q = actualQuotientAlgEquiv.symm (normalizedLaurentEquiv.symm q) := rfl

theorem actualQuotientAlgEquiv_symm_mk (p : A) :
    actualQuotientAlgEquiv.symm (Ideal.Quotient.mk (cofactorIdeal normalized) p) =
      Ideal.Quotient.mk (cofactorIdeal matrix) (forwardMap p) := rfl

/-- The abstract pullback denominator is the explicit gauge-normalized denominator
in the actual upper permanent quotient. -/
theorem actualDenom_eq_explicit : actualDenom =
    Ideal.Quotient.mk (cofactorIdeal matrix)
      (forwardMap (denom (matrix 1 3) (matrix 2 1))) := by
  have hd : normalizedLaurentEquiv.symm splitNormalDenom =
      Ideal.Quotient.mk (cofactorIdeal normalized) (denom (matrix 1 3) (matrix 2 1)) :=
    (AlgEquiv.symm_apply_eq normalizedLaurentEquiv).mpr normalizedLaurentEquiv_denom.symm
  rw [actualDenom,actualLaurentEquiv_symm_apply,hd,actualQuotientAlgEquiv_symm_mk]

end
end UniformFullChart
#print axioms UniformFullChart.actualDenom_eq_explicit
