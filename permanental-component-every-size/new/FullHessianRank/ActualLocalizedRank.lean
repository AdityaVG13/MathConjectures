import FullHessianRank.ActualRank
import GeometryBridge.LocalizedJacobian

set_option autoImplicit false
namespace ComponentFullHessianRank
noncomputable section
open Matrix MvPolynomial ComponentChartJacobian ComponentAmbientHessian

attribute [local instance] RingHom.ker_isPrime

theorem actual_ambient_rank_eq_of_localized_membership (k : ℕ)
    (S : Type*) [CommRing S] [Algebra (P k) S]
    [IsLocalization.AtPrime S (RingHom.ker (MvPolynomial.aeval (R := ℂ) (seed k)).toRingHom)]
    (hmem : ∀ i : Variables k, algebraMap (P k) S (pderiv i (actualPolynomial k)) ∈
      (Ideal.span (Set.range (generator k))).map (algebraMap (P k) S)) :
    Matrix.rank (hessian k) = 5 * (k + 1) + 3 := by
  apply actual_ambient_rank_eq_of_local_membership k
  exact UniformComponentGeometry.denominators_of_local_membership
    (MvPolynomial.aeval (R := ℂ) (seed k)).toRingHom
    (Ideal.span (Set.range (generator k))) (fun i => pderiv i (actualPolynomial k)) hmem

#print axioms actual_ambient_rank_eq_of_localized_membership
end
end ComponentFullHessianRank
