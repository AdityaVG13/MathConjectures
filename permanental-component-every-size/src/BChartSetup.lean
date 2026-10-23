import ConcreteLocalSetup

/-! Actual corrected b-chart polynomial matrix. The coordinate x3 is b; the
independent error x11 is in entry (2,1). Rows 2, 3, and 4 are cleared by D.
This file asserts no chart equivalence, ideal equality, or dimension claim. -/

namespace BChartLocalGeometry
open MvPolynomial ConcreteLocalGeometry

noncomputable def denominatorWithParameter (T : P) : P :=
  (T * (1 - x 3)) * (1 - (T + 1) * x 1) * (1 + T * x 2)

/-- The displayed cleared matrix N of the corrected b-coordinate chart. -/
noncomputable def matrixWithParameter (T : P) : Matrix (Fin 5) (Fin 5) P :=
  let da' := 1 - (T + 1) * x 1
  let dd' := 1 + T * x 2
  let e' := T * (1 - x 3)
  let den' := e' * da' * dd'
  let qn' := -x 3 * (1 + 2 * T) * da' * dd'
  let jn' := T * (1 + x 1) * e' * dd'
  let zn' := T * (1 + x 2) * e' * da'
  !![1, 1, 1, 1, x 1;
     1, x 4, -1 - x 2 + x 5, x 2, x 6;
     den', qn' - den' + den' * x 11, den' * (1 + x 7),
       den' - qn' + den' * x 8, den' * (x 1 + x 9);
     jn' + den' * x 10, den' * x 3,
       jn' + zn' - T * den' + den' * x 12, den', den';
     T * den', den' * x 3 + den' * x 13,
       zn' + den' * x 14, den', -den' + den' * x 15]

/-- Translation to the actual origin over any complex base parameter s. -/
noncomputable def matrixAt (s : ℂ) : Matrix (Fin 5) (Fin 5) P :=
  matrixWithParameter (MvPolynomial.C s + x 0)

noncomputable def denominatorAt (s : ℂ) : P :=
  denominatorWithParameter (MvPolynomial.C s + x 0)

/-- All twenty-five actual deleted-row/deleted-column order-four permanents. -/
noncomputable def equation (s : ℂ) (ij : Fin 5 × Fin 5) : P :=
  ((matrixAt s).submatrix ij.1.succAbove ij.2.succAbove).permanent

noncomputable def criticalIdeal (s : ℂ) : Ideal P :=
  Ideal.span (Set.range (equation s))

noncomputable def localCritical (s : ℂ) : Ideal Local :=
  Ideal.map (algebraMap P Local) (criticalIdeal s)

end BChartLocalGeometry
