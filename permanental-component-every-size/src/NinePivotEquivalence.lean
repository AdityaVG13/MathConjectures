import NinePivotNormalization

namespace PermanentGauge
variable {R : Type*} [CommRing R]

abbrev NormalizedSlice (R : Type*) [CommRing R] :=
  {M : Matrix (Fin 5) (Fin 5) R // ∀ k : Fin 9, M (pivot k).1 (pivot k).2 = 1}
abbrev PivotFiber (u : Fin 9 → Rˣ) :=
  {M : Matrix (Fin 5) (Fin 5) R // ∀ k : Fin 9, M (pivot k).1 (pivot k).2 = (u k : R)}

theorem inverse_pivot_factor (u : Fin 9 → Rˣ) (k : Fin 9) :
    (rowFactor u (pivot k).1)⁻¹ * (colFactor u (pivot k).2)⁻¹ = u k := by
  have he := congrArg (fun v : Rˣ =>
    (rowFactor u (pivot k).1)⁻¹ * (colFactor u (pivot k).2)⁻¹ * v) (pivot_factor u k)
  simpa [mul_assoc, mul_left_comm, mul_comm] using he.symm

theorem reconstruct_pivots (u : Fin 9 → Rˣ) (M : Matrix (Fin 5) (Fin 5) R)
    (h : ∀ k, M (pivot k).1 (pivot k).2 = 1) (k : Fin 9) :
    reconstruct u M (pivot k).1 (pivot k).2 = (u k : R) := by
  have he := congrArg (fun v : Rˣ => (v : R)) (inverse_pivot_factor u k)
  simpa [reconstruct, scaleMatrix, h] using he

/-- A genuine bijection on matrices for each fixed tuple of unit pivots.
It is not yet an equivalence of polynomial coordinate rings or local rings. -/
noncomputable def pivotFiberEquiv (u : Fin 9 → Rˣ) : PivotFiber u ≃ NormalizedSlice R where
  toFun M := ⟨normalize u M.val, normalize_pivots u M.val M.property⟩
  invFun M := ⟨reconstruct u M.val, reconstruct_pivots u M.val M.property⟩
  left_inv M := Subtype.ext (reconstruct_normalize u M.val)
  right_inv M := Subtype.ext (normalize_reconstruct u M.val)

abbrev PivotOpen (R : Type*) [CommRing R] :=
  {M : Matrix (Fin 5) (Fin 5) R // ∀ k : Fin 9, IsUnit (M (pivot k).1 (pivot k).2)}

noncomputable def pivotUnits (M : PivotOpen R) : Fin 9 → Rˣ :=
  fun k => (M.property k).unit

theorem pivotUnits_value (M : PivotOpen R) (k : Fin 9) :
    (pivotUnits M k : R) = M.val (pivot k).1 (pivot k).2 :=
  (M.property k).unit_spec

noncomputable def reconstructOpen (u : Fin 9 → Rˣ) (N : NormalizedSlice R) : PivotOpen R :=
  ⟨reconstruct u N.val, by
    intro k
    rw [reconstruct_pivots u N.val N.property k]
    exact (u k).isUnit⟩

theorem pivotUnits_reconstructOpen (u : Fin 9 → Rˣ) (N : NormalizedSlice R) :
    pivotUnits (reconstructOpen u N) = u := by
  funext k
  apply Units.ext
  rw [pivotUnits_value]
  exact reconstruct_pivots u N.val N.property k

/-- The unit-pivot open chart as a set of R-valued matrices, with all nine
unit coordinates retained. This theorem alone does not transport local rings. -/
noncomputable def pivotOpenEquiv : PivotOpen R ≃ (Fin 9 → Rˣ) × NormalizedSlice R where
  toFun M := (pivotUnits M, ⟨normalize (pivotUnits M) M.val, by
    apply normalize_pivots
    intro k
    exact (pivotUnits_value M k).symm⟩)
  invFun p := reconstructOpen p.1 p.2
  left_inv M := Subtype.ext (reconstruct_normalize (pivotUnits M) M.val)
  right_inv p := by
    apply Prod.ext
    · exact pivotUnits_reconstructOpen p.1 p.2
    · apply Subtype.ext
      change normalize (pivotUnits (reconstructOpen p.1 p.2))
        (reconstruct p.1 p.2.val) = p.2.val
      rw [pivotUnits_reconstructOpen, normalize_reconstruct]

#print axioms pivotFiberEquiv
#print axioms pivotOpenEquiv
end PermanentGauge
