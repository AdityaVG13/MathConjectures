import ActualLocalChart.IdealEquality
import GeometryBridge.SpreadEquality
import Mathlib.RingTheory.Noetherian.Basic

set_option autoImplicit false
namespace ComponentActualLocalChart
noncomputable section
open MvPolynomial ComponentChartJacobian
attribute [local instance] RingHom.ker_isPrime

/-- The actual gradient/cofactor scheme and the explicit chart coincide on an
actual principal open containing the specified seed, not just on its local ring. -/
theorem actual_ideal_equality_on_principal_open (k : ℕ) :
    ∃ s : P k, eval (seed k) s ≠ 0 ∧
      (actualGradientIdeal k).map (algebraMap (P k) (Localization.Away s)) =
      (Ideal.span (Set.range (generator k))).map
        (algebraMap (P k) (Localization.Away s)) := by
  let p := RingHom.ker (aeval (R := ℂ) (seed k)).toRingHom
  obtain ⟨s, hs, heq⟩ :=
    UniformComponentGeometry.exists_away_ideal_eq_of_atPrime_eq
      (actualGradientIdeal k) (Ideal.span (Set.range (generator k))) p
      (IsNoetherian.noetherian _) (IsNoetherian.noetherian _)
      (actual_local_ideal_equality k (Localization.AtPrime p))
  exact ⟨s, hs, heq⟩

#print axioms actual_ideal_equality_on_principal_open
end
end ComponentActualLocalChart
