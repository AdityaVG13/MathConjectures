import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Abstract local Nakayama equality certificate

This file proves only an abstract ideal-theoretic implication. It does not
establish finite generation, containment, or the displayed generation identity
for any particular polynomial ideals or localizations.

Ideal addition is written `⊔`, the join in the lattice of ideals. Thus
`J = I ⊔ IsLocalRing.maximalIdeal R * J` means `J = I + m J`.
No Noetherian hypothesis is needed beyond the explicit finite generation of `J`.
-/

namespace LocalGeometry

variable {R : Type*} [CommRing R]

/-- Nakayama's containment criterion for ideals and an ideal contained in the
Jacobson radical. Only the larger ideal must be finitely generated. -/
theorem ideal_le_of_le_sup_mul_of_le_jacobson
    {I J K : Ideal R} (hJ : J.FG)
    (hK : K ≤ Ideal.jacobson (⊥ : Ideal R))
    (hgen : J ≤ I ⊔ K * J) : J ≤ I := by
  apply Submodule.le_of_le_smul_of_le_jacobson_bot hJ hK
  simpa only [Ideal.smul_eq_mul] using hgen

/-- If `I ⊆ J`, `J` is finitely generated, and `J = I + m J` in a
commutative local ring with maximal ideal `m`, then `I = J`. -/
theorem ideal_eq_of_eq_sup_maximalIdeal_mul [IsLocalRing R]
    {I J : Ideal R} (hIJ : I ≤ J) (hJ : J.FG)
    (hgen : J = I ⊔ IsLocalRing.maximalIdeal R * J) : I = J := by
  apply le_antisymm hIJ
  exact ideal_le_of_le_sup_mul_of_le_jacobson hJ
    (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R)) hgen.le

end LocalGeometry

#print LocalGeometry.ideal_le_of_le_sup_mul_of_le_jacobson
#print axioms LocalGeometry.ideal_le_of_le_sup_mul_of_le_jacobson
#print LocalGeometry.ideal_eq_of_eq_sup_maximalIdeal_mul
#print axioms LocalGeometry.ideal_eq_of_eq_sup_maximalIdeal_mul
