import ActualLocalChart.IdealEquality
import ActualLocalChart.SmoothnessBridge
import DimensionClosure.ComponentChart

namespace ComponentActualLocalChart
noncomputable section
open MvPolynomial Matrix ComponentChartJacobian
attribute [local instance] RingHom.ker_isPrime

abbrev seedPrime (k : ℕ) : Ideal (P k) := RingHom.ker (aeval (R := ℂ) (seed k)).toRingHom
instance (k : ℕ) : (seedPrime k).IsPrime := RingHom.ker_isPrime _
abbrev AmbientLocal (k : ℕ) := Localization.AtPrime (seedPrime k)
def explicitChartIdeal (k : ℕ) : Ideal (P k) := Ideal.span (Set.range (generator k))
abbrev ExplicitQuotient (k : ℕ) := P k ⧸ explicitChartIdeal k
abbrev ExplicitLocalQuotient (k : ℕ) := AmbientLocal k ⧸
  (explicitChartIdeal k).map (algebraMap (P k) (AmbientLocal k))
abbrev ActualLocalQuotient (k : ℕ) := AmbientLocal k ⧸
  (actualGradientIdeal k).map (algebraMap (P k) (AmbientLocal k))

theorem selected_injective (k : ℕ) : Function.Injective (selected k) := by
  intro i j hij
  by_contra hn
  apply jacobian_det_ne_zero k
  exact Matrix.det_zero_of_column_eq hn (fun r => by simp [jacobian, hij])

def chartPresentation (k : ℕ) :
    Algebra.PreSubmersivePresentation ℂ (ExplicitQuotient k) (Variables k) (Generators k) :=
  Algebra.PreSubmersivePresentation.naive (v := generator k) (selected k) (selected_injective k)

def selectedDetPolynomial (k : ℕ) : P k :=
  (Matrix.of (fun i j : Generators k => pderiv (selected k i) (generator k j))).det

theorem presentation_jacobian (k : ℕ) : (chartPresentation k).jacobian =
    Ideal.Quotient.mk (explicitChartIdeal k) (selectedDetPolynomial k) := by
  have hm : (chartPresentation k).jacobiMatrix =
      Matrix.of (fun i j : Generators k => pderiv (selected k i) (generator k j)) := by
    funext i j
    exact Algebra.PreSubmersivePresentation.jacobiMatrix_naive
      (selected k) (selected_injective k) _ _ i j
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hm]
  rfl

theorem selectedDet_nonzero (k : ℕ) : eval (seed k) (selectedDetPolynomial k) ≠ 0 := by
  have he : eval (seed k) (selectedDetPolynomial k) = (jacobian k).transpose.det := by
    rw [selectedDetPolynomial, RingHom.map_det]
    rfl
  rw [he, Matrix.det_transpose]
  exact jacobian_det_ne_zero k

theorem chart_jacobian_mem (k : ℕ) : (chartPresentation k).jacobian ∈
    Algebra.algebraMapSubmonoid (ExplicitQuotient k) (seedPrime k).primeCompl := by
  rw [presentation_jacobian]
  exact ⟨selectedDetPolynomial k, selectedDet_nonzero k, rfl⟩

/-- The actual local quotient defined by the explicit chart equations is formally smooth. -/
theorem explicit_local_formallySmooth (k : ℕ) :
    Algebra.FormallySmooth ℂ (ExplicitLocalQuotient k) := by
  letI : IsScalarTower ℂ (ExplicitQuotient k) (ExplicitLocalQuotient k) :=
    IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := ExplicitQuotient k)
      (A := ExplicitLocalQuotient k) (by
      ext x
      change Ideal.Quotient.mk ((explicitChartIdeal k).map (algebraMap (P k) (AmbientLocal k)))
        (algebraMap ℂ (AmbientLocal k) x) =
        Ideal.Quotient.mk ((explicitChartIdeal k).map (algebraMap (P k) (AmbientLocal k)))
          (algebraMap (P k) (AmbientLocal k) (algebraMap ℂ (P k) x))
      rw [IsScalarTower.algebraMap_apply ℂ (P k) (AmbientLocal k)])
  exact UniformComponentGeometry.formallySmooth_localization_of_jacobian_mem
    (chartPresentation k)
    (Algebra.algebraMapSubmonoid (ExplicitQuotient k) (seedPrime k).primeCompl)
    (chart_jacobian_mem k)

/-- The actual gradient/cofactor local quotient at the seed is formally smooth over ℂ.
This uses equality of the actual localized ideals, not equality of their radicals. -/
theorem actual_local_formallySmooth (k : ℕ) :
    Algebra.FormallySmooth ℂ (ActualLocalQuotient k) := by
  letI : Algebra.FormallySmooth ℂ (ExplicitLocalQuotient k) := explicit_local_formallySmooth k
  change Algebra.FormallySmooth ℂ (AmbientLocal k ⧸
    (actualGradientIdeal k).map (algebraMap (P k) (AmbientLocal k)))
  haveI : Algebra.FormallySmooth ℂ (AmbientLocal k ⧸
      (Ideal.span (Set.range (generator k))).map (algebraMap (P k) (AmbientLocal k))) :=
    explicit_local_formallySmooth k
  exact Algebra.FormallySmooth.of_equiv
    (Ideal.quotientEquivAlgOfEq ℂ (actual_local_ideal_equality k (AmbientLocal k)).symm)

abbrev ActualQuotient (k : ℕ) := P k ⧸ actualGradientIdeal k

theorem actualGradientIdeal_le_seedPrime (k : ℕ) : actualGradientIdeal k ≤ seedPrime k := by
  apply Ideal.span_le.mpr
  rintro _ ⟨x, rfl⟩
  exact UniformComponentGeometry.eval_eq_zero_of_local_span_membership
    (S := AmbientLocal k) (seed k) (generator k) _
    (ComponentChartJacobian.generator_vanishes_at_seed k)
    (actual_local_gradient_membership k (AmbientLocal k) x)

def quotientSeedEval (k : ℕ) : ActualQuotient k →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ (actualGradientIdeal k) (aeval (seed k))
    (actualGradientIdeal_le_seedPrime k)

abbrev quotientSeedPrime (k : ℕ) : Ideal (ActualQuotient k) :=
  RingHom.ker (quotientSeedEval k).toRingHom

theorem seedComplement_image (k : ℕ) :
    Algebra.algebraMapSubmonoid (ActualQuotient k) (seedPrime k).primeCompl =
      (quotientSeedPrime k).primeCompl := by
  ext z
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact hr
  · intro hz
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨r, hz, rfl⟩

/-- The actual cofactor/gradient scheme is smooth at its specified seed prime. -/
theorem actual_isSmoothAt_seed (k : ℕ) : Algebra.IsSmoothAt ℂ (quotientSeedPrime k) := by
  letI : IsScalarTower ℂ (ActualQuotient k) (ActualLocalQuotient k) :=
    IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := ActualQuotient k)
      (A := ActualLocalQuotient k) (by
      ext x
      change Ideal.Quotient.mk ((actualGradientIdeal k).map (algebraMap (P k) (AmbientLocal k)))
        (algebraMap ℂ (AmbientLocal k) x) =
        Ideal.Quotient.mk ((actualGradientIdeal k).map (algebraMap (P k) (AmbientLocal k)))
          (algebraMap (P k) (AmbientLocal k) (algebraMap ℂ (P k) x))
      rw [IsScalarTower.algebraMap_apply ℂ (P k) (AmbientLocal k)])
  letI : IsLocalization (quotientSeedPrime k).primeCompl (ActualLocalQuotient k) := by
    rw [← seedComplement_image]
    infer_instance
  letI : Algebra.FormallySmooth ℂ (ActualLocalQuotient k) := actual_local_formallySmooth k
  exact Algebra.FormallySmooth.of_equiv (R := ℂ) (A := ActualLocalQuotient k)
    ((IsLocalization.algEquiv (quotientSeedPrime k).primeCompl
      (ActualLocalQuotient k) (Localization.AtPrime (quotientSeedPrime k))).restrictScalars ℂ)

#print axioms actual_isSmoothAt_seed
#print axioms actual_local_formallySmooth
end
end ComponentActualLocalChart
