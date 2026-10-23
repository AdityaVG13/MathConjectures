import CofactorScaling

namespace PermanentGauge
variable {R : Type*} [CommRing R]

/-- The nine edges of a fixed spanning tree, in emath066 order. -/
def pivot : Fin 9 → Fin 5 × Fin 5 :=
  ![(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,3),(3,4),(4,3)]

def rowFactor (u : Fin 9 → Rˣ) : Fin 5 → Rˣ :=
  ![1, u 0 / u 4, u 0 / u 5, u 3 / u 6, u 3 / u 8]
def colFactor (u : Fin 9 → Rˣ) : Fin 5 → Rˣ :=
  ![(u 0)⁻¹, (u 1)⁻¹, (u 2)⁻¹, (u 3)⁻¹, u 6 / (u 3 * u 7)]

theorem pivot_factor (u : Fin 9 → Rˣ) (k : Fin 9) :
    rowFactor u (pivot k).1 * colFactor u (pivot k).2 * u k = 1 := by
  fin_cases k <;> simp [pivot, rowFactor, colFactor, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

noncomputable def normalize (u : Fin 9 → Rˣ) (M : Matrix (Fin 5) (Fin 5) R) :=
  scaleMatrix (fun i => (rowFactor u i : R)) (fun j => (colFactor u j : R)) M
noncomputable def reconstruct (u : Fin 9 → Rˣ) (M : Matrix (Fin 5) (Fin 5) R) :=
  scaleMatrix (fun i => (((rowFactor u i)⁻¹ : Rˣ) : R))
    (fun j => (((colFactor u j)⁻¹ : Rˣ) : R)) M

theorem normalize_pivots (u : Fin 9 → Rˣ) (M : Matrix (Fin 5) (Fin 5) R)
    (h : ∀ k, M (pivot k).1 (pivot k).2 = (u k : R)) (k : Fin 9) :
    normalize u M (pivot k).1 (pivot k).2 = 1 := by
  have he := congrArg (fun v : Rˣ => (v : R)) (pivot_factor u k)
  simpa [normalize, scaleMatrix, h] using he

theorem reconstruct_normalize (u : Fin 9 → Rˣ) (M : Matrix (Fin 5) (Fin 5) R) :
    reconstruct u (normalize u M) = M := by
  ext i j
  simp [reconstruct, normalize, scaleMatrix, mul_assoc, mul_left_comm, mul_comm]

theorem normalize_reconstruct (u : Fin 9 → Rˣ) (M : Matrix (Fin 5) (Fin 5) R) :
    normalize u (reconstruct u M) = M := by
  ext i j
  simp [reconstruct, normalize, scaleMatrix, mul_assoc, mul_left_comm, mul_comm]

theorem normalize_cofactorIdeal (u : Fin 9 → Rˣ) (M : Matrix (Fin 5) (Fin 5) R) :
    cofactorIdeal (normalize u M) = cofactorIdeal M :=
  cofactorIdeal_scaleMatrix (rowFactor u) (colFactor u) M

#print axioms normalize_pivots
#print axioms reconstruct_normalize
#print axioms normalize_reconstruct
#print axioms normalize_cofactorIdeal
end PermanentGauge
