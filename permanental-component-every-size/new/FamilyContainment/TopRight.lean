import FamilyContainment.DiagonalMinors
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false
namespace ComponentFamilyContainment
open Matrix
variable {R : Type*} [CommRing R]

/-- Any bijective ordering of the remaining columns is valid. -/
theorem top_right_minor_zero {k : ℕ} (U : Matrix (Fin 3) (Fin 3) R)
    (v : Fin 3 → R) (lam : Fin (k+1) → R)
    (W : Matrix (Fin (k+1)) (Fin (k+1)) R) (i : Fin 3) (j : Fin (k+1))
    (e : (Fin 2 ⊕ Fin (k+1)) ≃ (Fin 3 ⊕ Fin k)) :
    ((family U v lam W).submatrix (Sum.map i.succAbove id)
      ((Sum.map id j.succAbove) ∘ e)).permanent = 0 := by
  classical
  unfold Matrix.permanent
  apply Finset.sum_eq_zero
  intro σ _
  by_contra hprod
  have htop (l : Fin 3) : ∃ a : Fin 2, σ (e.symm (Sum.inl l)) = Sum.inl a := by
    cases hh : σ (e.symm (Sum.inl l)) with
    | inl a => exact ⟨a, rfl⟩
    | inr b =>
      apply False.elim
      apply hprod
      apply Finset.prod_eq_zero (Finset.mem_univ (e.symm (Sum.inl l)))
      simp [Matrix.submatrix, hh, family]
  choose f hf using htop
  have hinj : Function.Injective f := by
    intro a b hab
    have hh : σ (e.symm (Sum.inl a)) = σ (e.symm (Sum.inl b)) := by
      rw [hf a, hf b, hab]
    exact Sum.inl.inj (e.symm.injective (σ.injective hh))
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hc
  omega

#print axioms top_right_minor_zero
end ComponentFamilyContainment
