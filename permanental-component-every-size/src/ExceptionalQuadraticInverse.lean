import FormalSquareRoot

set_option autoImplicit false
namespace ExceptionalBranchHelper

/-- Construct the simple j=1 branch of a quadratic over genuine formal series.
The coefficients may depend on any collection of independent formal parameters. -/
theorem exists_unique_quadratic_branch {σ : Type*}
    (A B C : MvPowerSeries σ ℂ)
    (hA : MvPowerSeries.constantCoeff A = -2)
    (hB : MvPowerSeries.constantCoeff B = 2)
    (hC : MvPowerSeries.constantCoeff C = 0) :
    ∃! j : MvPowerSeries σ ℂ,
      A*j^2+B*j+C = 0 ∧ MvPowerSeries.constantCoeff j = 1 := by
  let Δ := B^2-4*A*C
  have hΔ : MvPowerSeries.constantCoeff Δ = 4 := by
    norm_num [Δ,hA,hB,hC,map_ofNat]
  obtain ⟨w, hw, _⟩ := exists_unique_square_root_four Δ hΔ
  have hu : IsUnit (2*A) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff,isUnit_iff_ne_zero]
    norm_num [hA,map_ofNat]
  let u := hu.unit
  have huval : (u : MvPowerSeries σ ℂ) = 2*A := hu.unit_spec
  let j := -(B+w)*(↑(u⁻¹) : MvPowerSeries σ ℂ)
  have hj : 2*A*j = -(B+w) := by
    rw [← huval]
    simp [j,mul_comm,mul_left_comm,mul_assoc]
  have hjc : MvPowerSeries.constantCoeff j = 1 := by
    have he := congrArg MvPowerSeries.constantCoeff hj
    simp only [map_mul,map_ofNat,hA,map_neg,map_add,hB,hw.2] at he
    linear_combination -(1/4 : ℂ)*he
  have hsq : 2*A*j+B = -w := by rw [hj]; ring
  have he : 4*A*(A*j^2+B*j+C) = 0 := by
    calc
      _ = (2*A*j+B)^2-Δ := by dsimp [Δ]; ring
      _ = 0 := by rw [hsq,neg_sq,hw.1,sub_self]
  have h4 : IsUnit (4*A) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff,isUnit_iff_ne_zero]
    norm_num [hA,map_ofNat]
  have hr : A*j^2+B*j+C = 0 := h4.mul_left_cancel (by simpa using he)
  refine ⟨j,⟨hr,hjc⟩,?_⟩
  intro k hk
  have hv : IsUnit (A*(k+j)+B) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff,isUnit_iff_ne_zero]
    norm_num [hA,hB,hjc,hk.2,map_ofNat]
  have hz : (k-j)*(A*(k+j)+B) = 0 := by
    calc
      _ = (A*k^2+B*k+C)-(A*j^2+B*j+C) := by ring
      _ = 0 := by rw [hk.1,hr,sub_self]
  exact sub_eq_zero.mp (hv.mul_right_cancel (by simpa using hz))

#print axioms exists_unique_quadratic_branch
end ExceptionalBranchHelper
