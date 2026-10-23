import UpperGauge.CoordinateEquiv
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Quotient.Operations
namespace UniformUpperGauge
noncomputable section
open Matrix
def normalized : Matrix (Fin 3) (Fin 4) A := fun i j =>
  if IsPivot (i,j) then 1 else matrix i j
def cofactor (M : Matrix (Fin 3) (Fin 4) A) (c : Fin 4) : A :=
  (M.submatrix id c.succAbove).permanent
def cofactorIdeal (M : Matrix (Fin 3) (Fin 4) A) : Ideal A :=
  Ideal.span (Set.range (cofactor M))
def cofactorUnit (c : Fin 4) : Aˣ := (∏ i, rho i) * ∏ j : Fin 3, gamma (c.succAbove j)

theorem scale_pivot (i : Fin 3) (j : Fin 4) (h : IsPivot (i,j)) :
    (scale i j : A) = matrix i j := by
  rcases h with hi | hj
  · change i = 0 at hi
    subst i
    simpa [scale,rho,gamma,pivot] using units_value (Sum.inl j)
  · change j = 0 at hj
    subst j
    refine Fin.cases ?_ (fun r => ?_) i
    · simpa [scale,rho,gamma,pivot] using units_value (Sum.inl 0)
    · simpa [scale,rho,gamma,pivot,mul_assoc] using units_value (Sum.inr r)

theorem inverse_matrix_scaled (i : Fin 3) (j : Fin 4) :
    inverseMap (matrix i j) = (rho i : A) * (gamma j : A) * normalized i j := by
  rw [inverseMap_matrix]
  by_cases hp : IsPivot (i,j)
  · simp only [inverseImage,normalized,if_pos hp,mul_one]
    exact (scale_pivot i j hp).symm
  · simp [inverseImage,normalized,hp,scale]

theorem inverse_cofactor (c : Fin 4) :
    inverseMap (cofactor matrix c) = (cofactorUnit c : A) * cofactor normalized c := by
  simp only [cofactor,Matrix.permanent,map_sum,map_prod,Matrix.submatrix, Matrix.of_apply, id_eq,
    inverse_matrix_scaled,Finset.prod_mul_distrib,Equiv.prod_comp,
    cofactorUnit,Units.val_mul,Units.coe_prod,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Equiv.prod_comp σ (fun i => (rho i : A))]

theorem map_cofactorIdeal :
    Ideal.map inverseMap (cofactorIdeal matrix) = cofactorIdeal normalized := by
  simp only [cofactorIdeal,Ideal.span_range_eq_iSup,Ideal.map_iSup,Ideal.map_span,
    Set.image_singleton,inverse_cofactor]
  apply iSup_congr
  intro c
  exact Ideal.span_singleton_mul_left_unit (cofactorUnit c).isUnit _

def quotientRingEquiv : (A ⧸ cofactorIdeal matrix) ≃+* (A ⧸ cofactorIdeal normalized) :=
  Ideal.quotientEquiv _ _ coordinateRingEquiv.symm map_cofactorIdeal.symm

#print axioms quotientRingEquiv
end
end UniformUpperGauge
