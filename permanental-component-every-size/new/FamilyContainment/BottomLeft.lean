import FamilyContainment.OneCrossing
import FamilyContainment.DiagonalMinors

set_option backward.isDefEq.respectTransparency false
namespace ComponentFamilyContainment
open Matrix Equiv
variable {R : Type*} [CommRing R]

/-- Two specified left columns, followed by v, in the usual Fin 3 ordering. -/
def augmented (U : Matrix (Fin 3) (Fin 2) R) (v : Fin 3 → R) :
    Matrix (Fin 3) (Fin 3) R :=
  fun i j => Sum.elim (U i) (fun _ : Fin 1 => v i) (finSumFinEquiv.symm j)

theorem augmented_scaled_reordered_zero (U : Matrix (Fin 3) (Fin 2) R) (v : Fin 3 → R)
    (h : (augmented U v).permanent = 0) (t : R) (e : Fin 3 ≃ (Fin 2 ⊕ Fin 1)) :
    (Matrix.of (fun i j => Sum.elim (U i) (fun _ => v i * t) (e j))).permanent = 0 := by
  classical
  let A : Matrix (Fin 3) (Fin 3) R :=
    fun i j => Sum.elim (U i) (fun _ : Fin 1 => v i) (e j)
  have hA : A.permanent = 0 := by
    have he : A = (augmented U v).submatrix id (e.trans finSumFinEquiv) := by
      ext i j
      simp [A, augmented, Matrix.submatrix]
    rw [he, Matrix.permanent_permute_rows, h]
  let q := e.symm (Sum.inr (0 : Fin 1))
  have hAv : Matrix.updateCol A q v = A := by
    ext i j
    by_cases hj : j = q
    · subst j
      simp [A, q]
    · simp [Matrix.updateCol_ne hj]
  have he : (Matrix.of (fun i j => Sum.elim (U i) (fun _ => v i * t) (e j))) =
      Matrix.updateCol A q (t • v) := by
    ext i j
    by_cases hj : j = q
    · subst j
      simp [q, mul_comm]
    · rw [Matrix.updateCol_ne hj]
      cases hh : e j with
      | inl a => simp [A, hh]
      | inr b =>
        have hb : b = 0 := Fin.ext (by omega)
        have hjq : j = q := e.injective (by simp [q, hh, hb])
        exact (hj hjq).elim
  rw [he, Matrix.permanent_updateCol_smul, hAv, hA, mul_zero]

/-- The remaining family-minor case: delete a bottom row and a left column.
The maximal permanent of [U with that column removed, v] is the only upper hypothesis. -/
theorem bottom_left_minor_zero {k : ℕ} (U : Matrix (Fin 3) (Fin 3) R)
    (v : Fin 3 → R) (lam : Fin (k+1) → R)
    (W : Matrix (Fin (k+1)) (Fin (k+1)) R) (i : Fin (k+1)) (j : Fin 3)
    (h : (augmented (U.submatrix id j.succAbove) v).permanent = 0)
    (e : (Fin 3 ⊕ Fin k) ≃ (Fin 2 ⊕ Fin (k+1))) :
    ((family U v lam W).submatrix (Sum.map id i.succAbove)
      ((Sum.map j.succAbove id) ∘ e)).permanent = 0 := by
  have hh := crossing_zero (U.submatrix id j.succAbove) v
    (augmented_scaled_reordered_zero _ _ h) k lam (W.submatrix i.succAbove id) e
  convert hh using 1
  congr 1
  ext a b
  change family U v lam W (Sum.map id i.succAbove a)
    (Sum.map j.succAbove id (e b)) =
    crossing (U.submatrix id j.succAbove) v lam (W.submatrix i.succAbove id) a (e b)
  cases a <;> cases e b <;> rfl

#print axioms augmented_scaled_reordered_zero
#print axioms bottom_left_minor_zero
end ComponentFamilyContainment
