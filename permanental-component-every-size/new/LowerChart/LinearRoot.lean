import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

set_option autoImplicit false
namespace ComponentLowerChart
open Polynomial
variable {R : Type*} [CommRing R]

noncomputable def linearPolynomial (a : Rˣ) (b : R) : R[X] := C (a : R)*X+C b

theorem linear_root_eq (a : Rˣ) (b : R) :
    AdjoinRoot.root (linearPolynomial a b) =
      algebraMap R (AdjoinRoot (linearPolynomial a b)) (-(↑(a⁻¹) : R)*b) := by
  have h := AdjoinRoot.eval₂_root (linearPolynomial a b)
  change Polynomial.eval₂ (algebraMap R (AdjoinRoot (linearPolynomial a b)))
    (AdjoinRoot.root (linearPolynomial a b)) (C (a : R)*X+C b) = 0 at h
  have h' : algebraMap R (AdjoinRoot (linearPolynomial a b)) (a : R) *
      AdjoinRoot.root (linearPolynomial a b) + algebraMap R (AdjoinRoot (linearPolynomial a b)) b = 0 := by
    simpa only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X] using h
  have ha : IsUnit (algebraMap R (AdjoinRoot (linearPolynomial a b)) (a : R)) :=
    a.isUnit.map _
  apply ha.mul_left_cancel
  rw [← map_mul]
  have hc : (a : R)* (-(↑(a⁻¹) : R)*b) = -b := by
    calc
      _ = -((a : R)*(↑(a⁻¹) : R))*b := by ring
      _ = -b := by simp
  rw [hc, map_neg]
  exact eq_neg_of_add_eq_zero_left h'

noncomputable def linearRootEquiv (a : Rˣ) (b : R) :
    AdjoinRoot (linearPolynomial a b) ≃ₐ[R] R := by
  let f : AdjoinRoot (linearPolynomial a b) →ₐ[R] R :=
    AdjoinRoot.liftAlgHom _ (AlgHom.id R R) (-(↑(a⁻¹) : R)*b) (by
      simp [linearPolynomial, mul_assoc])
  let g : R →ₐ[R] AdjoinRoot (linearPolynomial a b) := Algebra.ofId _ _
  apply AlgEquiv.ofAlgHom f g
  · ext
  · apply AdjoinRoot.algHom_ext
    simp [f, g, linear_root_eq]

#print axioms linearRootEquiv
end ComponentLowerChart
