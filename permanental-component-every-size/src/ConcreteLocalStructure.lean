import ConcreteLocalEquality
import TargetLocalStructure
namespace ConcreteLocalGeometry

theorem localCritical_eq_three_primes :
    localCritical = localAxisIdeal 1 ⊓ (localAxisIdeal 2 ⊓ localAxisIdeal 3) := by
  rw [localCritical_eq_localTarget]
  exact localTarget_eq_axes_intersection

theorem localCritical_isRadical : localCritical.IsRadical := by
  rw [localCritical_eq_localTarget]
  exact localTarget_isRadical

#print axioms localCritical_eq_three_primes
#print axioms localCritical_isRadical
#print localCritical_eq_localTarget
end ConcreteLocalGeometry
