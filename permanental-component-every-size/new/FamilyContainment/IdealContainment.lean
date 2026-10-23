import FamilyContainment.FinCofactors
import Mathlib.RingTheory.Ideal.Quotient.Basic

set_option backward.isDefEq.respectTransparency false
namespace ComponentFamilyContainment
open Matrix Equiv
variable {R S : Type*} [CommRing R] [CommRing S]

theorem permanent_map {α : Type*} [Fintype α] [DecidableEq α]
    (f : R →+* S) (A : Matrix α α R) :
    (A.map f).permanent = f A.permanent := by
  simp [Matrix.permanent, Matrix.map_apply, map_sum, map_prod]

theorem augmented_map (f : R →+* S) (U : Matrix (Fin 3) (Fin 2) R) (v : Fin 3 → R) :
    augmented (U.map f) (f ∘ v) = (augmented U v).map f := by
  ext i j
  change Sum.elim (fun a => f (U i a)) (fun _ : Fin 1 => f (v i))
    (finSumFinEquiv.symm j) =
    f (Sum.elim (U i) (fun _ : Fin 1 => v i) (finSumFinEquiv.symm j))
  cases (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3).symm j <;> rfl

theorem familyFin_map {k : ℕ} (f : R →+* S) (U : Matrix (Fin 3) (Fin 3) R)
    (v : Fin 3 → R) (lam : Fin (k+1) → R)
    (W : Matrix (Fin (k+1)) (Fin (k+1)) R) :
    familyFin (U.map f) (f ∘ v) (f ∘ lam) (W.map f) = (familyFin U v lam W).map f := by
  ext a b
  change family (U.map f) (f ∘ v) (f ∘ lam) (W.map f)
    (familyIndexEquiv k a) (familyIndexEquiv k b) =
    f (family U v lam W (familyIndexEquiv k a) (familyIndexEquiv k b))
  cases familyIndexEquiv k a <;> cases familyIndexEquiv k b <;> simp [family]

/-- Scheme-theoretic pullback containment: every substituted submaximal
permanent belongs to every ideal containing the four upper equations and per W.
This is stronger than vanishing at points and uses no Nullstellensatz.
It does not by itself identify an ambient chart ideal. -/
theorem all_fin_cofactors_mem_ideal {k : ℕ} (I : Ideal R)
    (U : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R) (lam : Fin (k+1) → R)
    (W : Matrix (Fin (k+1)) (Fin (k+1)) R)
    (hW : W.permanent ∈ I) (hU : U.permanent ∈ I)
    (hB : ∀ j : Fin 3, (augmented (U.submatrix id j.succAbove) v).permanent ∈ I)
    (r c : Fin (3+k+1)) :
    ((familyFin U v lam W).submatrix r.succAbove c.succAbove).permanent ∈ I := by
  let f := Ideal.Quotient.mk I
  have hW0 : (W.map f).permanent = 0 := by
    rw [permanent_map]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hW
  have hU0 : (U.map f).permanent = 0 := by
    rw [permanent_map]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hU
  have hB0 (j : Fin 3) :
      (augmented ((U.map f).submatrix id j.succAbove) (f ∘ v)).permanent = 0 := by
    change (augmented ((U.submatrix id j.succAbove).map f) (f ∘ v)).permanent = 0
    rw [augmented_map, permanent_map]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hB j)
  have hh := all_fin_cofactors_zero (U.map f) (f ∘ v) (f ∘ lam) (W.map f) hW0 hU0 hB0 r c
  rw [familyFin_map] at hh
  change (((familyFin U v lam W).submatrix r.succAbove c.succAbove).map f).permanent = 0 at hh
  rw [permanent_map] at hh
  exact Ideal.Quotient.eq_zero_iff_mem.mp hh

#print axioms all_fin_cofactors_mem_ideal
end ComponentFamilyContainment
