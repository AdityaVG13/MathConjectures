import Mathlib.Basic.Complex.Basic
import ExceptionalCofactorDerivative
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Spectrum.Prime.Basic

set_option autoImplicit false
namespace UniformPermanentalObjects

abbrev Coordinates (n : ℕ) := Fin (n+1) × Fin (n+1)
abbrev Ring (n : ℕ) := MvPolynomial (Coordinates n) ℂ

noncomputable def genericMatrix (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) (Ring n) :=
  fun i j => MvPolynomial.X (i,j)

noncomputable def permanentPolynomial (n : ℕ) : Ring n := (genericMatrix n).permanent

noncomputable def cofactor (n : ℕ) (ij : Coordinates n) : Ring n :=
  ((genericMatrix n).submatrix ij.1.succAbove ij.2.succAbove).permanent

noncomputable def cofactorIdeal (n : ℕ) : Ideal (Ring n) :=
  Ideal.span (Set.range (cofactor n))

abbrev CoordinateAlgebra (n : ℕ) := Ring n ⧸ cofactorIdeal n

/-- The actual gradient of the generic permanent is its unsigned cofactor list.
The index n denotes matrices of size n+1, with cofactors of size n. -/
theorem derivative_permanent (n : ℕ) (ij : Coordinates n) :
    MvPolynomial.pderiv ij (permanentPolynomial n) = cofactor n ij := by
  unfold permanentPolynomial cofactor
  convert ExceptionalCofactorDerivative.permanent_derivative_single
    ij (genericMatrix n) ij.1 ij.2 1 ?_ using 1
  · simp
  · intro r c
    rcases ij with ⟨a, b⟩
    simp [genericMatrix, MvPolynomial.pderiv_X, Prod.mk.injEq, eq_comm, Pi.single_apply]

noncomputable def jacobianCofactors (n : ℕ) :
    Matrix (Coordinates n) (Coordinates n) (Ring n) :=
  fun ij kl => MvPolynomial.pderiv kl (cofactor n ij)

/-- This identifies the cofactor Jacobian with the actual second derivatives,
not with a surrogate matrix specified by the expected rank. -/
theorem jacobian_is_hessian (n : ℕ) (ij kl : Coordinates n) :
    jacobianCofactors n ij kl =
      MvPolynomial.pderiv kl (MvPolynomial.pderiv ij (permanentPolynomial n)) := by
  rw [derivative_permanent]
  rfl

theorem derivative_cofactor_same_row (n : ℕ) (ij : Coordinates n)
    (c : Fin (n+1)) : MvPolynomial.pderiv (ij.1,c) (cofactor n ij) = 0 := by
  apply ExceptionalCofactorDerivative.permanent_derivative_zero
  intro r s
  simp [genericMatrix, Matrix.submatrix, MvPolynomial.pderiv_X,
    Pi.single_apply, Prod.mk.injEq, Fin.succAbove_ne, eq_comm]

theorem derivative_cofactor_same_col (n : ℕ) (ij : Coordinates n)
    (r : Fin (n+1)) : MvPolynomial.pderiv (r,ij.2) (cofactor n ij) = 0 := by
  apply ExceptionalCofactorDerivative.permanent_derivative_zero
  intro s c
  simp [genericMatrix, Matrix.submatrix, MvPolynomial.pderiv_X,
    Pi.single_apply, Prod.mk.injEq, Fin.succAbove_ne, eq_comm]

theorem derivative_cofactor_surviving (n : ℕ) (ij : Coordinates (n+1))
    (r c : Fin (n+1)) :
    MvPolynomial.pderiv (ij.1.succAbove r,ij.2.succAbove c) (cofactor (n+1) ij) =
      (((genericMatrix (n+1)).submatrix ij.1.succAbove ij.2.succAbove).submatrix
        r.succAbove c.succAbove).permanent := by
  unfold cofactor
  convert ExceptionalCofactorDerivative.permanent_derivative_single
    (ij.1.succAbove r,ij.2.succAbove c)
    ((genericMatrix (n+1)).submatrix ij.1.succAbove ij.2.succAbove) r c 1 ?_ using 1
  · simp
  · intro a b
    simp [genericMatrix, Matrix.submatrix, MvPolynomial.pderiv_X,
      Pi.single_apply, Prod.mk.injEq, eq_comm]

#print axioms derivative_cofactor_same_row
#print axioms derivative_cofactor_same_col
#print axioms derivative_cofactor_surviving
#print axioms derivative_permanent
#print axioms jacobian_is_hessian
end UniformPermanentalObjects
