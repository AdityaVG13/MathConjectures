import FamilyContainment.IdealContainment

set_option backward.isDefEq.respectTransparency false
namespace ComponentFamilyContainment
open Matrix Equiv
variable {R : Type*} [CommRing R]

/-- The actual ambient block matrix, with no rank-one substitution. -/
def ambientFin {k : ℕ} (U : Matrix (Fin 3) (Fin 3) R)
    (V : Matrix (Fin 3) (Fin (k+1)) R) (L : Matrix (Fin (k+1)) (Fin 3) R)
    (W : Matrix (Fin (k+1)) (Fin (k+1)) R) :
    Matrix (Fin (3+k+1)) (Fin (3+k+1)) R :=
  (Matrix.fromBlocks U V L W).submatrix (familyIndexEquiv k) (familyIndexEquiv k)

/-- Actual ambient-ideal containment on the chart where V 0 0 is a unit
modulo I. This is not merely containment after a rank-one substitution.
The hypotheses are precisely membership of the lower-left entries, upper and
lower permanents, and the rank-one chart relations. -/
theorem ambient_cofactors_mem_ideal {k : ℕ} (I : Ideal R)
    (U : Matrix (Fin 3) (Fin 3) R) (V : Matrix (Fin 3) (Fin (k+1)) R)
    (L : Matrix (Fin (k+1)) (Fin 3) R) (W : Matrix (Fin (k+1)) (Fin (k+1)) R)
    (hunit : IsUnit (Ideal.Quotient.mk I (V 0 0)))
    (hL : ∀ a c, L a c ∈ I)
    (hW : W.permanent ∈ I) (hU : U.permanent ∈ I)
    (hB : ∀ j : Fin 3, (augmented (U.submatrix id j.succAbove) (fun i => V i 0)).permanent ∈ I)
    (hRank : ∀ i j, V 0 0 * V i j - V i 0 * V 0 j ∈ I)
    (r c : Fin (3+k+1)) :
    ((ambientFin U V L W).submatrix r.succAbove c.succAbove).permanent ∈ I := by
  let f := Ideal.Quotient.mk I
  obtain ⟨u, hu⟩ := hunit
  let v : Fin 3 → R ⧸ I := fun i => f (V i 0)
  let lam : Fin (k+1) → R ⧸ I := fun j => ↑u⁻¹ * f (V 0 j)
  have hv (i : Fin 3) (j : Fin (k+1)) : v i * lam j = f (V i j) := by
    have hh : f (V 0 0) * f (V i j) = f (V i 0) * f (V 0 j) := by
      have hz := Ideal.Quotient.eq_zero_iff_mem.mpr (hRank i j)
      simpa only [map_sub, map_mul, sub_eq_zero] using hz
    calc
      v i * lam j = ↑u⁻¹ * (f (V i 0) * f (V 0 j)) := by dsimp [v, lam]; ring
      _ = ↑u⁻¹ * (↑u * f (V i j)) := by rw [hu, hh]
      _ = f (V i j) := by simp [← mul_assoc]
  have hW0 : (W.map f).permanent = 0 := by
    rw [permanent_map]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hW
  have hU0 : (U.map f).permanent = 0 := by
    rw [permanent_map]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hU
  have hB0 (j : Fin 3) :
      (augmented ((U.map f).submatrix id j.succAbove) v).permanent = 0 := by
    change (augmented ((U.submatrix id j.succAbove).map f) (f ∘ (fun i => V i 0))).permanent = 0
    rw [augmented_map, permanent_map]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hB j)
  have he : (ambientFin U V L W).map f = familyFin (U.map f) v lam (W.map f) := by
    ext a b
    change f (Matrix.fromBlocks U V L W (familyIndexEquiv k a) (familyIndexEquiv k b)) =
      family (U.map f) v lam (W.map f) (familyIndexEquiv k a) (familyIndexEquiv k b)
    cases familyIndexEquiv k a with
    | inl i =>
      cases familyIndexEquiv k b with
      | inl j => rfl
      | inr j => exact (hv i j).symm
    | inr i =>
      cases familyIndexEquiv k b with
      | inl j => exact Ideal.Quotient.eq_zero_iff_mem.mpr (hL i j)
      | inr j => rfl
  have hh := all_fin_cofactors_zero (U.map f) v lam (W.map f) hW0 hU0 hB0 r c
  rw [← he] at hh
  change (((ambientFin U V L W).submatrix r.succAbove c.succAbove).map f).permanent = 0 at hh
  rw [permanent_map] at hh
  exact Ideal.Quotient.eq_zero_iff_mem.mp hh

#print axioms ambient_cofactors_mem_ideal
end ComponentFamilyContainment
