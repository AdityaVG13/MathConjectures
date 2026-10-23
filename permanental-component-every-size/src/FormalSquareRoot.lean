import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-! A bounded all-orders support lemma. This constructs a distinguished square
root in genuine multivariate formal series; it asserts no permanent splitting
or coordinate correspondence. No finiteness of the variable type is needed. -/
namespace ExceptionalBranchHelper

private noncomputable def halfSeries : PowerSeries ℂ :=
  PowerSeries.binomialSeries ℂ (1 / 2 : ℚ)

private theorem halfSeries_sq : halfSeries ^ 2 = 1 + PowerSeries.X := by
  calc
    halfSeries ^ 2 = halfSeries * halfSeries := pow_two _
    _ = PowerSeries.binomialSeries ℂ ((1 / 2 : ℚ) + 1 / 2) :=
      (PowerSeries.binomialSeries_add (A := ℂ) (1 / 2 : ℚ) (1 / 2 : ℚ)).symm
    _ = PowerSeries.binomialSeries ℂ (1 : ℚ) := by norm_num
    _ = 1 + PowerSeries.X := by
      simpa using (PowerSeries.binomialSeries_nat (R := ℚ) (A := ℂ) 1)

/-- Two square roots with constant coefficient two coincide: their sum is a unit. -/
theorem square_root_four_unique {σ : Type*}
    {Δ S T : MvPowerSeries σ ℂ}
    (hS : S ^ 2 = Δ) (hSc : MvPowerSeries.constantCoeff S = 2)
    (hT : T ^ 2 = Δ) (hTc : MvPowerSeries.constantCoeff T = 2) : S = T := by
  have hu : IsUnit (S + T) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, map_add, hSc, hTc]
    norm_num
  have hz : (S - T) * (S + T) = 0 := by
    calc
      (S - T) * (S + T) = S ^ 2 - T ^ 2 := by ring
      _ = 0 := by rw [hS, hT, sub_self]
  exact sub_eq_zero.mp ((hu.mul_left_eq_zero).mp hz)

/-- The distinguished square root of a series with constant coefficient four.
The proof substitutes Δ/4−1 into the ordinary binomial series of exponent 1/2. -/
theorem exists_unique_square_root_four {σ : Type*}
    (Δ : MvPowerSeries σ ℂ) (hΔ : MvPowerSeries.constantCoeff Δ = 4) :
    ∃! S : MvPowerSeries σ ℂ, S ^ 2 = Δ ∧ MvPowerSeries.constantCoeff S = 2 := by
  let a : MvPowerSeries σ ℂ := MvPowerSeries.C (1 / 4 : ℂ) * Δ - 1
  have ha0 : MvPowerSeries.constantCoeff a = 0 := by
    simp [a, hΔ]
  have ha : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha0
  let H : MvPowerSeries σ ℂ := halfSeries.subst a
  have hH : H ^ 2 = 1 + a := by
    change (halfSeries.subst a) ^ 2 = 1 + a
    rw [← PowerSeries.subst_pow ha, halfSeries_sq]
    rw [PowerSeries.subst_add ha, PowerSeries.subst_X ha]
    congr 1
    rw [← PowerSeries.coe_substAlgHom ha]
    exact map_one _
  have hH0 : MvPowerSeries.constantCoeff H = 1 := by
    change MvPowerSeries.constantCoeff (halfSeries.subst a) = 1
    rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero ha0]
    simp [halfSeries]
  have hfour : (4 : MvPowerSeries σ ℂ) * MvPowerSeries.C (1 / 4 : ℂ) = 1 := by
    rw [show (4 : MvPowerSeries σ ℂ) = MvPowerSeries.C (4 : ℂ) by simpa using (map_natCast (MvPowerSeries.C (σ := σ) (R := ℂ)) 4).symm, ← map_mul]
    norm_num
  have hroot : (2 * H) ^ 2 = Δ := by
    calc
      (2 * H) ^ 2 = 4 * H ^ 2 := by ring
      _ = 4 * (1 + a) := by rw [hH]
      _ = (4 * MvPowerSeries.C (1 / 4 : ℂ)) * Δ := by dsimp [a]; ring
      _ = Δ := by rw [hfour, one_mul]
  have hc : MvPowerSeries.constantCoeff (2 * H) = 2 := by
    rw [map_mul, hH0, mul_one]
    exact map_natCast (MvPowerSeries.constantCoeff (σ := σ) (R := ℂ)) 2
  refine ⟨2 * H, ⟨hroot, hc⟩, ?_⟩
  intro T hT
  exact square_root_four_unique hT.1 hT.2 hroot hc

end ExceptionalBranchHelper
#print axioms ExceptionalBranchHelper.exists_unique_square_root_four
#print axioms ExceptionalBranchHelper.square_root_four_unique
