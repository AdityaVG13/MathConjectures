import AmbientPairing.ActualPairing
import AmbientRestriction.ActualHessian

namespace AmbientPairing
open MvPolynomial ComponentChartJacobian ComponentAmbientHessian
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Fix every non-L entry at the seed, and substitute q_a k_c in the L block. -/
def lowerSubstitution (k : ℕ) : Variables k → MvPolynomial (Fin (k+1)) ℂ
  | Sum.inr (Sum.inr (Sum.inl (a,c))) => X a * C (ComponentUpperSeed.k c)
  | x => C (seed k x)

/-- Exact polynomial equality, not merely equality of evaluations. -/
theorem shared_lower_restriction (k : ℕ) :
    aeval (lowerSubstitution k) (actualPolynomial k) =
      AmbientRestriction.ambientPolynomial ComponentUpperSeed.U ComponentUpperSeed.v
        ComponentUpperSeed.k (seedLambda k) (SparseSeed.finArrowhead k) := by
  unfold actualPolynomial AmbientRestriction.ambientPolynomial
  change (aeval (lowerSubstitution k)).toRingHom ((actualAmbient k).permanent) = _
  trans ((actualAmbient k).map (aeval (lowerSubstitution k)).toRingHom).permanent
  · exact (ComponentFamilyContainment.permanent_map (aeval (lowerSubstitution k)).toRingHom
      (actualAmbient k)).symm
  congr 1
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => simp [Matrix.map_apply, actualAmbient, entryEquiv, bVar, lowerSubstitution,
        seed, AmbientRestriction.ambientMatrix, ComponentUpperSeed.U, Matrix.submatrix]
    | inr j =>
      refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [Matrix.map_apply, actualAmbient, entryEquiv, bVar, vVar, lowerSubstitution,
          seed, AmbientRestriction.ambientMatrix, ComponentUpperSeed.v, seedLambda, mul_comm]
  | inr i => cases j <;>
      simp [Matrix.map_apply, actualAmbient, entryEquiv, lVar, wVar, lowerSubstitution,
        seed, AmbientRestriction.ambientMatrix]

def lowerDirection (k : ℕ) : Variables k → Fin (k+1) → ℂ
  | Sum.inr (Sum.inr (Sum.inl (b,c))), a => if b = a then ComponentUpperSeed.k c else 0
  | _, _ => 0

theorem lowerSubstitution_eval_zero (k : ℕ) (x : Variables k) :
    eval (fun _ => 0) (lowerSubstitution k x) = seed k x := by
  rcases x with x | (x | (⟨a,c⟩ | x)) <;> simp [lowerSubstitution, seed]

theorem lowerSubstitution_derivative (k : ℕ) (x : Variables k) (a : Fin (k+1)) :
    pderiv a (lowerSubstitution k x) = C (lowerDirection k x a) := by
  rcases x with x | (x | (⟨b,c⟩ | x))
  · simp [lowerSubstitution, lowerDirection]
  · simp [lowerSubstitution, lowerDirection]
  · by_cases h : b = a <;> simp [lowerSubstitution, lowerDirection, h]
  · simp [lowerSubstitution, lowerDirection]

end
end AmbientPairing
#print axioms AmbientPairing.shared_lower_restriction
#print axioms AmbientPairing.lowerSubstitution_derivative
