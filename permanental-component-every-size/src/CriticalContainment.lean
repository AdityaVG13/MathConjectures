import AxisIdeal
import AxisVanishing
namespace ConcreteLocalGeometry

theorem equation_mem_target (r c : Fin 5) : equation (r,c) ∈ targetIdeal := by
  apply mem_targetIdeal_of_axes_zero
  · simpa using axes_vanish 0 r c
  · simpa using axes_vanish 1 r c
  · simpa using axes_vanish 2 r c

theorem criticalIdeal_le_targetIdeal : criticalIdeal ≤ targetIdeal := by
  rw [criticalIdeal,Ideal.span_le]
  rintro _ ⟨⟨r,c⟩,rfl⟩
  exact equation_mem_target r c
#print axioms criticalIdeal_le_targetIdeal
end ConcreteLocalGeometry
