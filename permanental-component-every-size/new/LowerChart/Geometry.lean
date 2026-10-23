import LowerChart.UniformPivot
import Mathlib.RingTheory.Smooth.Locus

set_option autoImplicit false
namespace ComponentLowerChart
noncomputable section

theorem freeLower_card (k : ℕ) : Fintype.card (FreeLower k) = (k+1)^2-1 := by
  simp [FreeLower, LowerIndex, Fintype.card_subtype_compl, pow_two]

theorem lowerBase_dimension (k : ℕ) : ringKrullDim (LowerBase k) = (((k+1)^2-1 : ℕ) : WithBot ℕ∞) := by
  have hi : Function.Injective (algebraMap (LowerParameters k) (LowerBase k)) :=
    IsLocalization.injective (LowerBase k)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (pivotCoefficient_ne_zero k))
  rw [ComponentDimensionClosure.localization_dimension ℂ (LowerParameters k) (LowerBase k)
    (Submonoid.powers (pivotCoefficient k)) hi]
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp [ENat.card_eq_coe_fintype_card, freeLower_card, pow_two]

instance (k : ℕ) : Algebra.Smooth ℂ (LowerBase k) := by
  letI : Algebra.Smooth ℂ (LowerParameters k) := ⟨inferInstance, inferInstance⟩
  letI : Algebra.Smooth (LowerParameters k) (LowerBase k) :=
    Algebra.Smooth.of_isLocalization_Away (pivotCoefficient k)
  exact Algebra.Smooth.comp ℂ (LowerParameters k) (LowerBase k)

#print axioms lowerBase_dimension
end
end ComponentLowerChart
