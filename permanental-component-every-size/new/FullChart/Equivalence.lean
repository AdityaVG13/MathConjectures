import FullChart.Inverse
set_option backward.isDefEq.respectTransparency false
namespace UniformFullChart
noncomputable section
open MvPolynomial ComponentChartJacobian

theorem backward_forward (k : ℕ) :
    (backward k).comp (forward k) = RingHom.id (Ambient k) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (ambientPivot k))
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [forward,forwardQuot,forwardPoly,backward,backwardBase,
      backwardBaseQuot,backwardBasePoly,ambientCoordinates,baseCoordinates]
  · intro x
    exact backward_forward_entry k x

theorem forward_backwardBase (k : ℕ) :
    (forward k).comp (backwardBase k) = (C : Base k →+* Target k) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (basePivot k))
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [forward,forwardQuot,forwardPoly,backwardBase,
      backwardBaseQuot,backwardBasePoly,ambientCoordinates,baseCoordinates]
  · intro ij
    change forward k (backwardBase k (baseEntry k ij)) = C (baseEntry k ij)
    rw [backwardBase_entry,forward_entry]
    cases ij <;> rfl

theorem forward_backward (k : ℕ) :
    (forward k).comp (backward k) = RingHom.id (Target k) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change forward k (backward k (C a)) = C a
    rw [backward_C]
    exact RingHom.congr_fun (forward_backwardBase k) a
  · intro j
    change forward k (backward k (X j)) = X j
    rw [backward_X,forward_entry]
    change C (baseEntry k (.inl (0,3))) * C ((↑(baseUnit k)⁻¹) : Base k) * X j = X j
    rw [←baseUnit_value,←map_mul]
    simp

def eliminationRingEquiv (k : ℕ) : Ambient k ≃+* Target k :=
  { forward k with
    invFun := backward k
    left_inv := fun x => RingHom.congr_fun (backward_forward k) x
    right_inv := fun x => RingHom.congr_fun (forward_backward k) x }

def eliminationAlgEquiv (k : ℕ) : Ambient k ≃ₐ[ℂ] Target k :=
  { eliminationRingEquiv k with
    commutes' := by
      intro z
      change forward k (algebraMap (AmbientQuot k) (Ambient k)
        (Ideal.Quotient.mk (ambientIdeal k) (C z))) = _
      simp [forward,forwardQuot,forwardPoly,baseCoordinates]
      rfl }

#print axioms eliminationAlgEquiv
end
end UniformFullChart
