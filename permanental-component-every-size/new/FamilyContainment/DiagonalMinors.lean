import BlockPermanent.BlockPermanent

set_option backward.isDefEq.respectTransparency false
namespace ComponentFamilyContainment
open Matrix
variable {R : Type*} [CommRing R] {m : ℕ}

/-- The family map, with no support or invertibility assumptions. -/
def family (U : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R)
    (lam : Fin m → R) (W : Matrix (Fin m) (Fin m) R) :
    Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) R :=
  Matrix.fromBlocks U (fun i j => v i * lam j) 0 W

/-- Honest deletion of a top row and a left column factors, over any commutative ring. -/
theorem top_left_minor (U : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R)
    (lam : Fin m → R) (W : Matrix (Fin m) (Fin m) R) (i j : Fin 3) :
    ((family U v lam W).submatrix (Sum.map i.succAbove id)
      (Sum.map j.succAbove id)).permanent =
      (U.submatrix i.succAbove j.succAbove).permanent * W.permanent := by
  have h : (family U v lam W).submatrix (Sum.map i.succAbove id)
      (Sum.map j.succAbove id) =
      Matrix.fromBlocks (U.submatrix i.succAbove j.succAbove)
        (fun a b => v (i.succAbove a) * lam b) 0 W := by
    ext (a | a) (b | b) <;> rfl
  rw [h, ComponentBlockPermanent.permanent_fromBlocks_zero_lower]

/-- Honest deletion of a bottom row and a right column factors. -/
theorem bottom_right_minor {k : ℕ} (U : Matrix (Fin 3) (Fin 3) R)
    (v : Fin 3 → R) (lam : Fin (k+1) → R)
    (W : Matrix (Fin (k+1)) (Fin (k+1)) R) (i j : Fin (k+1)) :
    ((family U v lam W).submatrix (Sum.map id i.succAbove)
      (Sum.map id j.succAbove)).permanent =
      U.permanent * (W.submatrix i.succAbove j.succAbove).permanent := by
  have h : (family U v lam W).submatrix (Sum.map id i.succAbove)
      (Sum.map id j.succAbove) = Matrix.fromBlocks U
      (fun a b => v a * lam (j.succAbove b)) 0
      (W.submatrix i.succAbove j.succAbove) := by
    ext (a | a) (b | b) <;> rfl
  rw [h, ComponentBlockPermanent.permanent_fromBlocks_zero_lower]

theorem top_left_minor_zero (U : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R)
    (lam : Fin m → R) (W : Matrix (Fin m) (Fin m) R) (hW : W.permanent = 0)
    (i j : Fin 3) :
    ((family U v lam W).submatrix (Sum.map i.succAbove id)
      (Sum.map j.succAbove id)).permanent = 0 := by
  rw [top_left_minor, hW, mul_zero]

theorem bottom_right_minor_zero {k : ℕ} (U : Matrix (Fin 3) (Fin 3) R)
    (v : Fin 3 → R) (lam : Fin (k+1) → R)
    (W : Matrix (Fin (k+1)) (Fin (k+1)) R) (hU : U.permanent = 0)
    (i j : Fin (k+1)) :
    ((family U v lam W).submatrix (Sum.map id i.succAbove)
      (Sum.map id j.succAbove)).permanent = 0 := by
  rw [bottom_right_minor, hU, zero_mul]

#print axioms top_left_minor_zero
#print axioms bottom_right_minor_zero
end ComponentFamilyContainment
