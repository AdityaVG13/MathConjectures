import FullChart.RetainedQuotient
import UpperGauge.ActualChart
import LowerChart.ActualCoordinates
import Mathlib.RingTheory.Localization.Ideal

set_option backward.isDefEq.respectTransparency false
namespace UniformFullChart
noncomputable section
open MvPolynomial ComponentChartJacobian
open scoped TensorProduct

theorem lowerRawIdeal_eq_actual (k : ℕ) : lowerRawIdeal k = ComponentLowerChart.actualIdeal k := by
  rw [lowerRawIdeal_singleton]
  rfl

def lowerRawQuotEquiv (k : ℕ) : LowerRawQuot k ≃ₐ[ℂ] ComponentLowerChart.ActualQuotient k :=
  Ideal.quotientEquivAlgOfEq ℂ (lowerRawIdeal_eq_actual k)

@[simp] theorem lowerRawQuotEquiv_mk (k : ℕ) (p : MvPolynomial (WIndex k) ℂ) :
    lowerRawQuotEquiv k (Ideal.Quotient.mk (lowerRawIdeal k) p) =
      Ideal.Quotient.mk (ComponentLowerChart.actualIdeal k) p :=
  Ideal.quotientEquivAlgOfEq_mk ℂ (lowerRawIdeal_eq_actual k) p

def retainedActualTensorEquiv (k : ℕ) :
    BaseQuot k ≃ₐ[ℂ] UpperRawQuot ⊗[ℂ] ComponentLowerChart.ActualQuotient k :=
  (retainedTensorEquiv k).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : UpperRawQuot ≃ₐ[ℂ] UpperRawQuot)
      (lowerRawQuotEquiv k))

@[simp] theorem retainedActualTensorEquiv_upper (k : ℕ) (p : MvPolynomial BIndex ℂ) :
    retainedActualTensorEquiv k (Ideal.Quotient.mk (baseIdeal k) (rename Sum.inl p)) =
      (Algebra.TensorProduct.includeLeft : UpperRawQuot →ₐ[ℂ]
        UpperRawQuot ⊗[ℂ] ComponentLowerChart.ActualQuotient k)
        (Ideal.Quotient.mk upperRawIdeal p) := by
  simp [retainedActualTensorEquiv]

@[simp] theorem retainedActualTensorEquiv_lower (k : ℕ) (p : MvPolynomial (WIndex k) ℂ) :
    retainedActualTensorEquiv k (Ideal.Quotient.mk (baseIdeal k) (rename Sum.inr p)) =
      (Algebra.TensorProduct.includeRight : ComponentLowerChart.ActualQuotient k →ₐ[ℂ]
        UpperRawQuot ⊗[ℂ] ComponentLowerChart.ActualQuotient k)
        (Ideal.Quotient.mk (ComponentLowerChart.actualIdeal k) p) := by
  simp [retainedActualTensorEquiv]

/-- The six upper row/column pivots, in the actual upper permanent quotient. -/
def upperRawDelta : UpperRawQuot := Ideal.Quotient.mk upperRawIdeal UniformUpperGauge.delta
abbrev UpperRawLocalized := Localization.Away upperRawDelta
abbrev UpperMappedQuot := UniformUpperGauge.A ⧸
  upperRawIdeal.map (algebraMap UniformUpperGauge.P UniformUpperGauge.A)
abbrev UpperActualQuot := UniformUpperGauge.A ⧸ UniformUpperGauge.cofactorIdeal UniformUpperGauge.matrix

theorem upperActualIdeal_map_raw :
    UniformUpperGauge.cofactorIdeal UniformUpperGauge.matrix =
      Ideal.map (algebraMap UniformUpperGauge.P UniformUpperGauge.A) upperRawIdeal := by
  simp only [UniformUpperGauge.cofactorIdeal,upperRawIdeal,Ideal.map_span,←Set.range_comp]
  congr 2
  funext c
  simp only [Function.comp_apply,UniformUpperGauge.cofactor,upperRawEquation,Matrix.permanent,
    map_sum,map_prod,Matrix.submatrix,Matrix.of_apply,id_eq,UniformUpperGauge.matrix,
    ComponentUpperSeed.genericB]

instance upperMappedQuot_localization : IsLocalization.Away upperRawDelta UpperMappedQuot := by
  simpa [upperRawDelta,Algebra.algebraMapSubmonoid,Submonoid.map_powers] using
    (inferInstance : IsLocalization
      (Algebra.algebraMapSubmonoid UpperRawQuot (Submonoid.powers UniformUpperGauge.delta)) UpperMappedQuot)

instance upperMappedQuot_tower : IsScalarTower ℂ UpperRawQuot UpperMappedQuot :=
  IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := UpperRawQuot) (A := UpperMappedQuot) (by
    ext z
    rfl)

/-- Localizing the actual raw four-permanent quotient at the six pivots gives exactly
the upper coefficient quotient used by the actual gauge chart. -/
def upperActualQuotEquiv : UpperActualQuot ≃ₐ[ℂ] UpperRawLocalized :=
  (Ideal.quotientEquivAlgOfEq ℂ upperActualIdeal_map_raw).trans
    ((IsLocalization.algEquiv (Submonoid.powers upperRawDelta)
      UpperMappedQuot UpperRawLocalized).restrictScalars ℂ)


@[simp] theorem upperActualQuotEquiv_mk (p : UniformUpperGauge.P) :
    upperActualQuotEquiv (Ideal.Quotient.mk (UniformUpperGauge.cofactorIdeal UniformUpperGauge.matrix)
      (algebraMap UniformUpperGauge.P UniformUpperGauge.A p)) =
      algebraMap UpperRawQuot UpperRawLocalized (Ideal.Quotient.mk upperRawIdeal p) := by
  simp only [upperActualQuotEquiv,AlgEquiv.trans_apply,Ideal.quotientEquivAlgOfEq_mk]
  change (IsLocalization.algEquiv (Submonoid.powers upperRawDelta) UpperMappedQuot UpperRawLocalized)
    (algebraMap UpperRawQuot UpperMappedQuot (Ideal.Quotient.mk upperRawIdeal p)) = _
  exact (IsLocalization.algEquiv (Submonoid.powers upperRawDelta)
    UpperMappedQuot UpperRawLocalized).commutes _

@[simp] theorem upperActualQuotEquiv_symm_mk (p : UniformUpperGauge.P) :
    upperActualQuotEquiv.symm
      (algebraMap UpperRawQuot UpperRawLocalized (Ideal.Quotient.mk upperRawIdeal p)) =
      Ideal.Quotient.mk (UniformUpperGauge.cofactorIdeal UniformUpperGauge.matrix)
        (algebraMap UniformUpperGauge.P UniformUpperGauge.A p) := by
  apply upperActualQuotEquiv.injective
  rw [AlgEquiv.apply_symm_apply,upperActualQuotEquiv_mk]


/-- Every row/column gauge pivot is a unit on the six-pivot raw upper chart. -/
theorem upperRawPivot_isUnit (p : UniformUpperGauge.Pivot) :
    IsUnit (algebraMap UpperRawQuot UpperRawLocalized
      (Ideal.Quotient.mk upperRawIdeal (X (UniformUpperGauge.pivot p)))) := by
  apply IsLocalization.Away.isUnit_of_dvd upperRawDelta
  exact map_dvd (Ideal.Quotient.mk upperRawIdeal)
    (Finset.dvd_prod_of_mem (fun q : UniformUpperGauge.Pivot =>
      (X (UniformUpperGauge.pivot q) : UniformUpperGauge.P)) (Finset.mem_univ p))

theorem upperRawB03_isUnit :
    IsUnit (algebraMap UpperRawQuot UpperRawLocalized
      (Ideal.Quotient.mk upperRawIdeal (X ((0,3) : BIndex)))) :=
  upperRawPivot_isUnit (.inl 3)

end
end UniformFullChart
#print axioms UniformFullChart.retainedActualTensorEquiv
#print axioms UniformFullChart.upperActualQuotEquiv
