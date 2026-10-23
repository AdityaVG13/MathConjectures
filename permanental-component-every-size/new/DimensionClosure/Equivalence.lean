import DimensionClosure.LocalizedComponents

set_option autoImplicit false
namespace ComponentDimensionClosure
variable {R S : Type*} [CommRing R] [CommRing S]

theorem minimalPrime_map_equiv (e : R ≃+* S) (P : Ideal R) (hP : IsMinimalPrime P) :
    IsMinimalPrime (P.map e.toRingHom) := by
  have he := Ideal.minimalPrimes_map_of_surjective (f := e.toRingHom) e.surjective (⊥ : Ideal R)
  have hk : RingHom.ker e.toRingHom = ⊥ := (RingHom.injective_iff_ker_eq_bot e.toRingHom).mp e.injective
  simp only [Ideal.map_bot, hk, bot_sup_eq] at he
  rw [show IsMinimalPrime (P.map e.toRingHom) ↔
    P.map e.toRingHom ∈ (⊥ : Ideal S).minimalPrimes from Iff.rfl, he]
  exact ⟨P,hP,rfl⟩

theorem component_dimensions_of_equiv (e : R ≃+* S) (d : ℕ)
    (h : ∀ Q : Ideal S, IsMinimalPrime Q → ringKrullDim (S ⧸ Q) = d)
    (P : Ideal R) (hP : IsMinimalPrime P) : ringKrullDim (R ⧸ P) = d := by
  let Q := P.map e.toRingHom
  have hQ : IsMinimalPrime Q := minimalPrime_map_equiv e P hP
  have eqv := Ideal.quotientEquiv P Q e rfl
  rw [ringKrullDim_eq_of_ringEquiv eqv]
  exact h Q hQ

#print axioms component_dimensions_of_equiv
end ComponentDimensionClosure
