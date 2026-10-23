import PolynomialCertificate
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
namespace PolynomialFamilyCertificate
variable {K : Type*} [Field K]

def inverseAt (s : K) : Matrix (Fin 15) (Fin 15) K :=
  (rankScale s)⁻¹ • scaledInverse s

theorem inverseAt_mul_selected (s : K) (h : rankScale s ≠ 0) :
    inverseAt s * selectedMatrix s = 1 := by
  rw [inverseAt, Matrix.smul_mul, scaledInverse_mul_selected, smul_smul,
    inv_mul_cancel₀ h, one_smul]

theorem selected_rank (s : K) (h : rankScale s ≠ 0) :
    (selectedMatrix s).rank = 15 := by
  apply le_antisymm (selectedMatrix s).rank_le_width
  have hr := Matrix.rank_mul_le_right (inverseAt s) (selectedMatrix s)
  simpa only [inverseAt_mul_selected s h, Matrix.rank_one, Fintype.card_fin] using hr

theorem coefficient_rank (s : K) (h : rankScale s ≠ 0) :
    (coefficientMatrix s).rank = 15 := by
  apply le_antisymm (coefficientMatrix s).rank_le_width
  have hr := Matrix.rank_submatrix_le (coefficientMatrix s) LocalGeometryRank.selectedRows id
  change (selectedMatrix s).rank ≤ (coefficientMatrix s).rank at hr
  exact (selected_rank s h).symm.le.trans hr

theorem rankScale_ne_zero_complex (s : ℂ) (hs : s ≠ 0) (he : s ≠ -(1/2 : ℂ)) :
    rankScale s ≠ 0 := by
  unfold rankScale
  apply mul_ne_zero
  · exact mul_ne_zero (by norm_num) (pow_ne_zero _ hs)
  · apply pow_ne_zero
    intro hz
    apply he
    linear_combination (1/2 : ℂ) * hz

theorem coefficient_rank_complex (s : ℂ) (hs : s ≠ 0) (he : s ≠ -(1/2 : ℂ)) :
    (coefficientMatrix s).rank = 15 :=
  coefficient_rank s (rankScale_ne_zero_complex s hs he)

#print axioms inverseAt_mul_selected
#print axioms coefficient_rank_complex
end PolynomialFamilyCertificate
