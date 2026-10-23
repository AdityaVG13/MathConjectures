import FullHessianRank.ChartMap
import FullHessianRank.GradientCofactors
import GeometryBridge.LocalizedJacobian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ComponentActualLocalChart
noncomputable section
open MvPolynomial Matrix ComponentChartJacobian ComponentAmbientHessian
open ComponentFamilyContainment ComponentFullHessianRank
attribute [local instance] RingHom.ker_isPrime

 theorem actual_local_gradient_membership (k : ℕ) (S : Type*) [CommRing S]
    [Algebra (P k) S]
    [IsLocalization.AtPrime S (RingHom.ker (aeval (R := ℂ) (seed k)).toRingHom)]
    (x : Variables k) :
    algebraMap (P k) S (pderiv x (actualPolynomial k)) ∈
      (Ideal.span (Set.range (generator k))).map (algebraMap (P k) S) := by
  let f := algebraMap (P k) S
  have hu : IsUnit ((blockV k).map f 0 0) := by
    change IsUnit (algebraMap (P k) S (blockV k 0 0))
    apply (IsLocalization.AtPrime.isUnit_to_map_iff S
      (RingHom.ker (aeval (R := ℂ) (seed k)).toRingHom) _).mpr
    change aeval (seed k) (blockV k 0 0) ≠ 0
    norm_num [blockV, bVar, seed, ComponentUpperSeed.B]
  have hle := ambient_submaximal_ideal_le_chart_of_unit
    ((blockU k).map f) ((blockV k).map f) ((blockL k).map f) ((blockW k).map f) hu
  rw [generator_ideal, ← chartIdeal_map f]
  rw [actual_gradient_eq_cofactor]
  let rc := finiteEntryEquiv k x
  have he : f (((finiteAmbient k).submatrix rc.1.succAbove rc.2.succAbove).permanent) =
      ((ambientFin ((blockU k).map f) ((blockV k).map f) ((blockL k).map f)
        ((blockW k).map f)).submatrix rc.1.succAbove rc.2.succAbove).permanent := by
    rw [ambientFin_map]
    exact (permanent_map f ((finiteAmbient k).submatrix rc.1.succAbove rc.2.succAbove)).symm
  change f (((finiteAmbient k).submatrix rc.1.succAbove rc.2.succAbove).permanent) ∈ _
  rw [he]
  exact hle (Ideal.subset_span ⟨rc, rfl⟩)

#print axioms actual_local_gradient_membership
end
end ComponentActualLocalChart
