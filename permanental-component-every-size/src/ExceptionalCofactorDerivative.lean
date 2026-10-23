import ExceptionalExpansion
import Mathlib.Algebra.MvPolynomial.PDeriv

/- General derivative infrastructure, following the cofactor argument in the
user's MathConjectures/PermanentPartition/Singular.lean, pinned commit
314de9626cb2ccae38d231349857876ebd507697. Not a novelty claim. -/
namespace ExceptionalCofactorDerivative
open MvPolynomial ExceptionalExpansion
variable {σ R : Type*} [DecidableEq σ] [CommRing R]

theorem permanent_derivative_zero {n : ℕ} (v : σ)
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ R))
    (h : ∀ r c, pderiv v (M r c) = 0) : pderiv v M.permanent = 0 := by
  rw [Matrix.permanent,map_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  refine Finset.prod_induction _ (fun f => pderiv v f = 0) ?_ ?_ ?_
  · intro f g hf hg
    rw [Derivation.leibniz,hf,hg,smul_zero,smul_zero,add_zero]
  · exact Derivation.map_one_eq_zero _
  · intro j _
    exact h (p j) j

theorem permanent_derivative_single {n : ℕ} (v : σ)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) (MvPolynomial σ R))
    (a b : Fin (n+1)) (D : MvPolynomial σ R)
    (h : ∀ r c, pderiv v (M r c) = if r=a ∧ c=b then D else 0) :
    pderiv v M.permanent = D*(M.submatrix a.succAbove b.succAbove).permanent := by
  classical
  have hminor (i : Fin (n+1)) :
      pderiv v (M.submatrix i.succAbove b.succAbove).permanent = 0 := by
    apply permanent_derivative_zero
    intro r c
    simp [Matrix.submatrix,h,Fin.succAbove_ne]
  rw [permanent_expand_column M b,map_sum]
  simp only [Derivation.leibniz,hminor,smul_eq_mul,mul_zero,zero_add,add_zero]
  rw [Finset.sum_eq_single a]
  · simp [h,mul_comm]
  · intro i _ hi
    simp [h,hi]
  · simp
end ExceptionalCofactorDerivative
#print axioms ExceptionalCofactorDerivative.permanent_derivative_single
