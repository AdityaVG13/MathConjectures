import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic

/- Standard diagonal-scaling algebra supporting the actual coordinate bridge.
This does not assert existence of an ambient local-ring coordinate equivalence. -/
namespace PermanentGauge
open Matrix

variable {R : Type*} [CommRing R]

noncomputable def scaleMatrix {n : Type*} (r c : n → R)
    (M : Matrix n n R) : Matrix n n R := fun i j => r i * c j * M i j

theorem permanent_scaleMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (r c : n → R) (M : Matrix n n R) :
    (scaleMatrix r c M).permanent =
      (∏ i, r i) * (∏ j, c j) * M.permanent := by
  simp only [Matrix.permanent, scaleMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  simp only [Finset.prod_mul_distrib, Equiv.prod_comp]

noncomputable def cofactor (M : Matrix (Fin 5) (Fin 5) R) (ij : Fin 5 × Fin 5) : R :=
  (M.submatrix ij.1.succAbove ij.2.succAbove).permanent

noncomputable def cofactorIdeal (M : Matrix (Fin 5) (Fin 5) R) : Ideal R :=
  Ideal.span (Set.range (cofactor M))

noncomputable def unitScale (r c : Fin 5 → Rˣ) (ij : Fin 5 × Fin 5) : Rˣ :=
  (∏ k : Fin 4, r (ij.1.succAbove k)) * (∏ k : Fin 4, c (ij.2.succAbove k))

theorem cofactor_scaleMatrix (r c : Fin 5 → Rˣ)
    (M : Matrix (Fin 5) (Fin 5) R) (ij : Fin 5 × Fin 5) :
    cofactor (scaleMatrix (fun i => (r i : R)) (fun j => (c j : R)) M) ij =
      (unitScale r c ij : R) * cofactor M ij := by
  change (scaleMatrix (fun k : Fin 4 => (r (ij.1.succAbove k) : R))
    (fun k : Fin 4 => (c (ij.2.succAbove k) : R))
    (M.submatrix ij.1.succAbove ij.2.succAbove)).permanent = _
  rw [permanent_scaleMatrix]
  simp [unitScale, cofactor]

/-- The actual ideal of all25 cofactors is unchanged by unit row/column scaling.
No assertion about arbitrary unit multiplication of a function's Jacobian is used. -/
theorem cofactorIdeal_scaleMatrix (r c : Fin 5 → Rˣ)
    (M : Matrix (Fin 5) (Fin 5) R) :
    cofactorIdeal (scaleMatrix (fun i => (r i : R)) (fun j => (c j : R)) M) =
      cofactorIdeal M := by
  simp only [cofactorIdeal, Ideal.span_range_eq_iSup]
  apply iSup_congr
  intro ij
  rw [cofactor_scaleMatrix]
  exact Ideal.span_singleton_mul_left_unit (unitScale r c ij).isUnit _

#print axioms permanent_scaleMatrix
#print axioms cofactorIdeal_scaleMatrix
end PermanentGauge
