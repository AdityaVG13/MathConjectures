import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace UniformComponentGeometry
variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

/-- Full column independence over the residue field supplies a coefficient left inverse,
without selecting any square minor of the rectangular matrix. -/
theorem exists_matrix_left_inverse_of_injective
    (A : Matrix ι κ K) (h : Function.Injective A.mulVec) :
    ∃ B : Matrix κ ι K, B * A = 1 := by
  obtain ⟨b, hb⟩ := (Matrix.toLin' A).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr h)
  refine ⟨LinearMap.toMatrix' b, ?_⟩
  have hm := congrArg LinearMap.toMatrix' hb
  simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
    LinearMap.toMatrix'_id] using hm

/-- Full column rank is actual injectivity of the matrix map. -/
theorem mulVec_injective_of_rank_eq_card
    (A : Matrix ι κ K) (h : A.rank = Fintype.card κ) :
    Function.Injective A.mulVec := by
  change Function.Injective A.mulVecLin
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  have hd := A.mulVecLin.finrank_range_add_finrank_ker
  rw [← Matrix.rank, h, Module.finrank_pi] at hd
  omega

/-- If the full Jacobian factors through r generators and has rank r, its coefficient matrix
has full column rank. No nonsingular-minor selection is needed. -/
theorem coefficient_injective_of_product_rank {ν : Type*} [Fintype ν]
    (A : Matrix ι κ K) (J : Matrix κ ν K) (h : (A * J).rank = Fintype.card κ) :
    Function.Injective A.mulVec := by
  apply mulVec_injective_of_rank_eq_card A
  exact le_antisymm A.rank_le_card_width (h ▸ Matrix.rank_mul_le_left A J)

variable {R : Type*} [CommRing R]
/-- Any coefficient preconditioner B whose square product B*A has unit determinant
produces a genuine left inverse to A over the current ring. -/
theorem exists_matrix_left_inverse_of_isUnit_product_det
    (A : Matrix ι κ R) (B : Matrix κ ι R) (h : IsUnit (B * A).det) :
    ∃ C : Matrix κ ι R, C * A = 1 := by
  refine ⟨(B * A)⁻¹ * B, ?_⟩
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h]

#print axioms coefficient_injective_of_product_rank
#print axioms exists_matrix_left_inverse_of_injective
#print axioms exists_matrix_left_inverse_of_isUnit_product_det
end UniformComponentGeometry
