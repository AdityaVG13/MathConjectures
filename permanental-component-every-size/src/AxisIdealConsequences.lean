import AxisIdeal

namespace ConcreteLocalGeometry

/-- Each coordinate-axis ideal is prime, as the kernel of its actual
    projection into the polynomial domain. -/
theorem axisIdeal_isPrime (k : Fin 16) : (axisIdeal k).IsPrime := by
  rw [axisIdeal_eq_ker]
  exact RingHom.ker_isPrime (axisProjection k)

/-- The actual target ideal is radical, using its proved intersection of
    the three prime coordinate ideals. This is not yet a statement about
    the critical ideal. -/
theorem targetIdeal_isRadical : targetIdeal.IsRadical := by
  rw [targetIdeal_eq_axes_intersection]
  exact (axisIdeal_isPrime 1).isRadical.inf
    ((axisIdeal_isPrime 2).isRadical.inf (axisIdeal_isPrime 3).isRadical)

end ConcreteLocalGeometry

#print axioms ConcreteLocalGeometry.axisIdeal_isPrime
#print axioms ConcreteLocalGeometry.targetIdeal_isRadical
