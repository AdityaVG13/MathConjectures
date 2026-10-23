import CofactorScaling
import Mathlib.RingTheory.Ideal.Maps

namespace PermanentGauge
variable {R S : Type*} [CommRing R] [CommRing S]

theorem cofactor_map (f : R →+* S) (M : Matrix (Fin 5) (Fin 5) R) (ij : Fin 5 × Fin 5) :
    f (cofactor M ij) = cofactor (fun i j => f (M i j)) ij := by
  simp [cofactor, Matrix.permanent, Matrix.submatrix]

theorem cofactorIdeal_map (f : R →+* S) (M : Matrix (Fin 5) (Fin 5) R) :
    Ideal.map f (cofactorIdeal M) = cofactorIdeal (fun i j => f (M i j)) := by
  rw [cofactorIdeal, Ideal.map_span, ← Set.range_comp]
  have he : f ∘ cofactor M = cofactor (fun i j => f (M i j)) := by
    funext ij
    exact cofactor_map f M ij
  rw [he]
  rfl

#print axioms cofactorIdeal_map
end PermanentGauge
