import ParametricTranslation

namespace ParametricLocalGeometry
open MvPolynomial ConcreteLocalGeometry

/-- The original displayed matrix formula with its parameter replaced by T.
    All other coordinate variables are literally unchanged. -/
noncomputable def matrixWithParameter (T : P) : Matrix (Fin 5) (Fin 5) P :=
  let da' := 1 - (T + 1) * x 1
  let dq' := 1 + MvPolynomial.C (2 : ℂ) * T - T * x 3
  let dd' := 1 + T * x 2
  let den' := da' * dq' * dd'
  let jn' := T * (1 + x 1) * dq' * dd'
  let kn' := -T * x 3 * da' * dd'
  let zn' := T * (1 + x 2) * da' * dq'
  !![1, 1, 1, 1, x 1;
     1, x 4, -1 - x 2 + x 5, x 2, x 6;
     1, x 3 - 1, 1 + x 7, 1 - x 3 + x 8, x 1 + x 9;
     jn' + den' * x 10, kn' + den' * x 11,
       jn' + zn' - T * den' + den' * x 12, den', den';
     T * den', kn' + den' * x 13, zn' + den' * x 14, den', -den' + den' * x 15]

theorem originalN_eq_matrixWithParameter : N = matrixWithParameter t := rfl

/-- Entrywise translation is exactly the displayed matrix with t replaced by s+x0. -/
theorem translatedN_eq_matrixWithParameter (s : ℂ) :
    translatedN s = matrixWithParameter (MvPolynomial.C s + x 0) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [translatedN, N, matrixWithParameter, jn, kn, zn, den, da, dq, dd, translation_t] <;> ring


end ParametricLocalGeometry

#print axioms ParametricLocalGeometry.originalN_eq_matrixWithParameter
#print axioms ParametricLocalGeometry.translatedN_eq_matrixWithParameter
