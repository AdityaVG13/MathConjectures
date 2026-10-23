import FamilyContainment.ChartIdeal

set_option autoImplicit false
namespace ComponentFullHessianRank
open Matrix ComponentFamilyContainment
variable {R S : Type*} [CommRing R] [CommRing S]

theorem ambientFin_map {k : ℕ} (f : R →+* S)
    (U : Matrix (Fin 3) (Fin 3) R) (V : Matrix (Fin 3) (Fin (k+1)) R)
    (L : Matrix (Fin (k+1)) (Fin 3) R) (W : Matrix (Fin (k+1)) (Fin (k+1)) R) :
    ambientFin (U.map f) (V.map f) (L.map f) (W.map f) =
      (ambientFin U V L W).map f := by
  ext i j
  change Matrix.fromBlocks (U.map f) (V.map f) (L.map f) (W.map f)
    (familyIndexEquiv k i) (familyIndexEquiv k j) =
    f (Matrix.fromBlocks U V L W (familyIndexEquiv k i) (familyIndexEquiv k j))
  cases familyIndexEquiv k i <;> cases familyIndexEquiv k j <;> rfl

theorem chartGenerators_map {k : ℕ} (f : R →+* S)
    (U : Matrix (Fin 3) (Fin 3) R) (V : Matrix (Fin 3) (Fin (k+1)) R)
    (L : Matrix (Fin (k+1)) (Fin 3) R) (W : Matrix (Fin (k+1)) (Fin (k+1)) R) :
    chartGenerators (U.map f) (V.map f) (L.map f) (W.map f) =
      f '' chartGenerators U V L W := by
  have ha (j : Fin 3) :
      (augmented ((U.map f).submatrix id j.succAbove) (fun i => f (V i 0))).permanent =
      f ((augmented (U.submatrix id j.succAbove) (fun i => V i 0)).permanent) := by
    change (augmented ((U.submatrix id j.succAbove).map f) (f ∘ (fun i => V i 0))).permanent = _
    rw [augmented_map, permanent_map]
  simp only [chartGenerators, Set.image_union, ← Set.range_comp, Set.image_insert_eq,
    Set.image_singleton, Function.comp_def, Matrix.map_apply, permanent_map, ha, map_sub, map_mul]

theorem chartIdeal_map {k : ℕ} (f : R →+* S)
    (U : Matrix (Fin 3) (Fin 3) R) (V : Matrix (Fin 3) (Fin (k+1)) R)
    (L : Matrix (Fin (k+1)) (Fin 3) R) (W : Matrix (Fin (k+1)) (Fin (k+1)) R) :
    chartIdeal (U.map f) (V.map f) (L.map f) (W.map f) =
      (chartIdeal U V L W).map f := by
  unfold chartIdeal
  rw [chartGenerators_map, Ideal.map_span]

#print axioms ambientFin_map
#print axioms chartIdeal_map
end ComponentFullHessianRank
