import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

set_option autoImplicit false
namespace ComponentFullHessianRank
open Matrix
variable {K V F : Type*} [Field K] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

/-- Exact matrix saddle criterion. The residual form is tested only on the
annihilator of the cross block, and need not be nondegenerate on all of F. -/
theorem saddle_isUnit (A : Matrix V F K) (Q : Matrix F F K)
    (hA : Function.Injective A.transpose.mulVec)
    (hQ : ∀ x : F → K, A.mulVec x = 0 →
      (∀ y : F → K, A.mulVec y = 0 → dotProduct y (Q.mulVec x) = 0) → x = 0) :
    IsUnit (Matrix.fromBlocks (0 : Matrix V V K) A A.transpose Q) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  change Function.Injective (Matrix.fromBlocks (0 : Matrix V V K) A A.transpose Q).mulVecLin
  apply (LinearMap.ker_eq_bot).mp
  apply Matrix.ker_mulVecLin_eq_bot_iff.mpr
  intro z hz
  have htop : A.mulVec (z ∘ Sum.inr) = 0 := by
    funext i
    have hi := congrFun hz (Sum.inl i)
    simpa [Matrix.fromBlocks_mulVec] using hi
  have hbottom : A.transpose.mulVec (z ∘ Sum.inl) + Q.mulVec (z ∘ Sum.inr) = 0 := by
    funext i
    have hi := congrFun hz (Sum.inr i)
    simpa [Matrix.fromBlocks_mulVec] using hi
  have hx : z ∘ Sum.inr = 0 := by
    apply hQ _ htop
    intro y hy
    have hh := congrArg (dotProduct y) hbottom
    simpa [dotProduct_add, Matrix.dotProduct_transpose_mulVec, hy] using hh
  have hv : z ∘ Sum.inl = 0 := by
    apply hA
    simpa [hx] using hbottom
  funext i
  cases i with
  | inl i => exact congrFun hv i
  | inr i => exact congrFun hx i

theorem saddle_rank (A : Matrix V F K) (Q : Matrix F F K)
    (hA : Function.Injective A.transpose.mulVec)
    (hQ : ∀ x : F → K, A.mulVec x = 0 →
      (∀ y : F → K, A.mulVec y = 0 → dotProduct y (Q.mulVec x) = 0) → x = 0) :
    (Matrix.fromBlocks (0 : Matrix V V K) A A.transpose Q).rank =
      Fintype.card V + Fintype.card F := by
  simpa using Matrix.rank_of_isUnit _ (saddle_isUnit A Q hA hQ)

#print axioms saddle_isUnit
#print axioms saddle_rank
end ComponentFullHessianRank
