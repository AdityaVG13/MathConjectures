import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Matrix.Mul

namespace UniformComponentGeometry

variable {R ν ι κ : Type*} [CommRing R] [Fintype κ]

/-- Differentiating an exact ideal-membership certificate at a common zero removes the
coefficient-derivative terms. This is the genuine polynomial Jacobian bridge. -/
theorem eval_pderiv_linear_combination
    (x : ν → R) (a g : κ → MvPolynomial ν R)
    (hg : ∀ j, MvPolynomial.eval x (g j) = 0) (k : ν) :
    MvPolynomial.eval x (MvPolynomial.pderiv k (∑ j, a j * g j)) =
      ∑ j, MvPolynomial.eval x (a j) *
        MvPolynomial.eval x (MvPolynomial.pderiv k (g j)) := by
  simp [map_sum, MvPolynomial.pderiv_mul, hg]

/-- A family of actual coefficient identities factors its evaluated polynomial Jacobian. -/
theorem eval_jacobian_of_coefficient_identities
    (x : ν → R) (A : Matrix ι κ (MvPolynomial ν R))
    (f : ι → MvPolynomial ν R) (g : κ → MvPolynomial ν R)
    (hfg : f = A.mulVec g) (hg : ∀ j, MvPolynomial.eval x (g j) = 0) :
    (fun i k => MvPolynomial.eval x (MvPolynomial.pderiv k (f i))) =
      (A.map (MvPolynomial.eval x)) *
        Matrix.of (fun j k => MvPolynomial.eval x (MvPolynomial.pderiv k (g j))) := by
  ext i k
  rw [hfg]
  exact eval_pderiv_linear_combination x (A i) g hg k

#print axioms eval_jacobian_of_coefficient_identities
end UniformComponentGeometry
