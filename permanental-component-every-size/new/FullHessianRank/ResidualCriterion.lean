import FullHessianRank.SaddleRank

set_option autoImplicit false
namespace ComponentFullHessianRank
open Matrix
variable {K V F R : Type*} [Field K] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] [Fintype R] [DecidableEq R]

/-- An exhaustive coordinate map for the annihilator converts an invertible
restricted matrix into exactly the residual hypothesis of the saddle theorem. -/
theorem residual_kernel_zero (A : Matrix V F K) (Q : Matrix F F K) (E : Matrix F R K)
    (hland : ∀ u, A.mulVec (E.mulVec u) = 0)
    (hexhaust : ∀ x, A.mulVec x = 0 → ∃ u, E.mulVec u = x)
    (hunit : IsUnit (E.transpose * Q * E))
    (x : F → K) (hx : A.mulVec x = 0)
    (hq : ∀ y, A.mulVec y = 0 → dotProduct y (Q.mulVec x) = 0) : x = 0 := by
  obtain ⟨u, rfl⟩ := hexhaust x hx
  have hu : (E.transpose * Q * E).mulVec u = 0 := by
    ext i
    have hi := hq (E.mulVec (Pi.single i 1)) (hland _)
    have hi' : dotProduct (Pi.single i 1) (E.transpose.mulVec (Q.mulVec (E.mulVec u))) = 0 := by
      rw [Matrix.dotProduct_transpose_mulVec]
      simpa [dotProduct_comm] using hi
    simpa [Matrix.mulVec_mulVec, dotProduct, Matrix.mul_assoc, Pi.single_apply] using hi'
  have hu0 : u = 0 := (Matrix.mulVec_injective_of_isUnit hunit) (by simpa using hu)
  simp [hu0]

theorem saddle_rank_of_restriction (A : Matrix V F K) (Q : Matrix F F K) (E : Matrix F R K)
    (hA : Function.Injective A.transpose.mulVec)
    (hland : ∀ u, A.mulVec (E.mulVec u) = 0)
    (hexhaust : ∀ x, A.mulVec x = 0 → ∃ u, E.mulVec u = x)
    (hunit : IsUnit (E.transpose * Q * E)) :
    (Matrix.fromBlocks (0 : Matrix V V K) A A.transpose Q).rank =
      Fintype.card V + Fintype.card F :=
  saddle_rank A Q hA (residual_kernel_zero A Q E hland hexhaust hunit)

#print axioms residual_kernel_zero
#print axioms saddle_rank_of_restriction
end ComponentFullHessianRank
