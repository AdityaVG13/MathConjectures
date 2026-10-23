import GeometryBridge.CoefficientJacobian
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

set_option autoImplicit false
namespace ComponentFullHessianRank
open MvPolynomial Matrix
variable {K ν ι κ : Type*} [Field K] [Fintype ν] [Fintype ι] [Fintype κ]

/-- Membership after multiplying by a polynomial nonzero at the point is
sufficient for the actual Jacobian rank bound. This is the local, not global,
ideal-containment statement needed for an open affine chart. -/
theorem jacobian_rank_le_of_local_membership (x : ν → K)
    (f : ι → MvPolynomial ν K) (g : κ → MvPolynomial ν K)
    (hg : ∀ j, eval x (g j) = 0)
    (hmem : ∀ i, ∃ s : MvPolynomial ν K, eval x s ≠ 0 ∧
      s * f i ∈ Ideal.span (Set.range g)) :
    Matrix.rank (fun i v => eval x (pderiv v (f i))) ≤ Fintype.card κ := by
  classical
  choose s hs hm using hmem
  have hf (i : ι) : eval x (f i) = 0 := by
    have hz : eval x (s i * f i) = 0 := by
      obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hm i)
      rw [← ha]
      simp [hg]
    exact (mul_eq_zero.mp (by simpa using hz)).resolve_left (hs i)
  choose A hA using fun i => Ideal.mem_span_range_iff_exists_fun.mp (hm i)
  let B : Matrix ι κ K := fun i j => (eval x (s i))⁻¹ * eval x (A i j)
  let J : Matrix κ ν K := fun j v => eval x (pderiv v (g j))
  have he : (fun i v => eval x (pderiv v (f i))) = B * J := by
    funext i v
    have hd := congrArg (fun p => eval x (pderiv v p)) (hA i)
    rw [UniformComponentGeometry.eval_pderiv_linear_combination] at hd
    simp only [pderiv_mul, map_add, map_mul, hf, mul_zero, zero_add] at hd
    change _ = ∑ j, ((eval x (s i))⁻¹ * eval x (A i j)) * eval x (pderiv v (g j))
    calc
      _ = (eval x (s i))⁻¹ * (eval x (s i) * eval x (pderiv v (f i))) := by
        rw [← mul_assoc, inv_mul_cancel₀ (hs i), one_mul]
      _ = _ := by rw [← hd, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    exact hg
  rw [he]
  exact le_trans (Matrix.rank_mul_le_left B J) B.rank_le_card_width

#print axioms jacobian_rank_le_of_local_membership
end ComponentFullHessianRank
