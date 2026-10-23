import BChartSetup
import GaugeFamilyPoint

namespace BChartTransport
open MvPolynomial
abbrev P25 := PermanentGauge.Coordinates.P
noncomputable def v (i j : Fin 5) : P25 := X (i,j)
noncomputable def assignment (s : ℂ) : Fin 16 → P25 :=
  ![v 4 0-C s,v 0 4,v 1 3,v 3 1,v 1 1,v 1 2+1,v 1 4,v 2 2-1,
    v 2 3-1,v 2 4,v 3 0-C s,v 2 1+1,v 3 2-C s,v 4 1,v 4 2-C s,v 4 4+1]
noncomputable def chartMap (s : ℂ) : ConcreteLocalGeometry.P →+* P25 :=
  eval₂Hom C (assignment s)
noncomputable def denominator : P25 :=
  (v 4 0*(1-v 3 1))*(1-(v 4 0+1)*v 0 4)*(1+v 4 0*v 1 3)
noncomputable def clearedMatrix (s : ℂ) : Matrix (Fin 5) (Fin 5) P25 :=
  let t := v 4 0
  let a := v 0 4
  let d := v 1 3
  let b := v 3 1
  let da := 1-(t+1)*a
  let dd := 1+t*d
  let e := t*(1-b)
  let D := e*da*dd
  let Q := -b*(1+2*t)*da*dd
  let J := t*(1+a)*e*dd
  let Z := t*(1+d)*e*da
  !![1,1,1,1,v 0 4;
     1,v 1 1,v 1 2-v 1 3,v 1 3,v 1 4;
     D,Q+D*v 2 1,D*v 2 2,D*v 2 3-Q,D*(v 0 4+v 2 4);
     J+D*(v 3 0-C s),D*v 3 1,J+Z-t*D+D*(v 3 2-C s),D,D;
     t*D,D*(v 3 1+v 4 1),Z+D*(v 4 2-C s),D,D*v 4 4]

/-- The actual cleared matrix, not a new independent copy asserted equal. -/
theorem matrix_correspondence (s : ℂ) :
    (fun i j => chartMap s (BChartLocalGeometry.matrixAt s i j)) = clearedMatrix s := by
  have htwo (f : ConcreteLocalGeometry.P →ₐ[ℂ] P25) : f (2 : ConcreteLocalGeometry.P) = 2 := by
    rw [show (2 : ConcreteLocalGeometry.P) = 1 + 1 by ring, map_add, map_one]
    ring
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chartMap, assignment, BChartLocalGeometry.matrixAt,
      BChartLocalGeometry.matrixWithParameter, ConcreteLocalGeometry.x, clearedMatrix, htwo] <;> ring

theorem denominator_correspondence (s : ℂ) :
    chartMap s (BChartLocalGeometry.denominatorAt s) = denominator := by
  simp [chartMap, assignment, BChartLocalGeometry.denominatorAt,
    BChartLocalGeometry.denominatorWithParameter, ConcreteLocalGeometry.x, denominator]

theorem ideal_correspondence (s : ℂ) :
    Ideal.map (chartMap s) (BChartLocalGeometry.criticalIdeal s) =
      PermanentGauge.cofactorIdeal (clearedMatrix s) := by
  rw [BChartLocalGeometry.criticalIdeal, Ideal.map_span, ← Set.range_comp]
  have he : chartMap s ∘ BChartLocalGeometry.equation s =
      PermanentGauge.cofactor (clearedMatrix s) := by
    funext ij
    have hm := matrix_correspondence s
    simp only [Function.comp_apply, BChartLocalGeometry.equation, PermanentGauge.cofactor,
      Matrix.permanent, map_sum, map_prod, Matrix.submatrix_apply]
    apply Finset.sum_congr rfl
    intro σ hσ
    apply Finset.prod_congr rfl
    intro k hk
    exact congrFun (congrFun hm (ij.1.succAbove (σ k))) (ij.2.succAbove k)
  rw [he]
  rfl

theorem assignment_at_family (s : ℂ) (k : Fin 16) :
    PermanentGauge.Coordinates.pointPoly s (assignment s k) = 0 := by
  fin_cases k <;> simp [assignment, v, PermanentGauge.Coordinates.pointPoly, PrimitiveFamily.A]

theorem point_composition (s : ℂ) :
    (PermanentGauge.Coordinates.pointPoly s).comp (chartMap s) = ConcreteLocalGeometry.evalOrigin := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [chartMap, ConcreteLocalGeometry.evalOrigin, PermanentGauge.Coordinates.pointPoly]
  · intro k
    simpa [chartMap, ConcreteLocalGeometry.evalOrigin] using assignment_at_family s k

#print axioms matrix_correspondence
#print axioms ideal_correspondence
#print axioms point_composition
end BChartTransport
