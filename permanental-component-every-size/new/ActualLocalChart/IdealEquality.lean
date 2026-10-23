import ActualLocalChart.Containment

set_option autoImplicit false
namespace ComponentActualLocalChart
noncomputable section
open MvPolynomial Matrix ComponentChartJacobian ComponentAmbientHessian ComponentFullHessianRank
attribute [local instance] RingHom.ker_isPrime

def actualGradientIdeal (k : ℕ) : Ideal (P k) :=
  Ideal.span (Set.range (fun x : Variables k => pderiv x (actualPolynomial k)))

/-- The actual gradient/cofactor scheme and the explicit chart equations have
identical ideals in the local ring at the specified seed. No reducedness is assumed. -/
theorem actual_local_ideal_equality (k : ℕ) (S : Type*) [CommRing S]
    [Algebra (P k) S]
    [IsLocalization.AtPrime S (RingHom.ker (aeval (R := ℂ) (seed k)).toRingHom)] :
    (actualGradientIdeal k).map (algebraMap (P k) S) =
      (Ideal.span (Set.range (generator k))).map (algebraMap (P k) S) := by
  apply UniformComponentGeometry.localized_polynomial_ideal_eq_of_local_containment
    (seed k) (actualGradientIdeal k) (generator k)
    (fun i : Generators k => pderiv (selected k i) (actualPolynomial k))
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨x,rfl⟩
    exact actual_local_gradient_membership k S x
  · intro i
    exact Ideal.subset_span ⟨selected k i, rfl⟩
  · exact generator_vanishes_at_seed k
  · exact actual_selected_gradient_jacobian_rank k

#print axioms actual_local_ideal_equality
end
end ComponentActualLocalChart
