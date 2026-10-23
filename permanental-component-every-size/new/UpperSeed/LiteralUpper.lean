import FamilyContainment.BottomLeft
import Mathlib.Tactic

set_option autoImplicit false
namespace ComponentLiteralUpper
variable {R : Type*} [CommRing R]

theorem augmented_is_literal_minor (B : Matrix (Fin 3) (Fin 4) R) (c : Fin 3) :
    ComponentFamilyContainment.augmented
      ((B.submatrix id Fin.castSucc).submatrix id c.succAbove) (fun i => B i 3) =
      B.submatrix id c.castSucc.succAbove := by
  ext i j
  fin_cases c <;> fin_cases j <;> rfl

theorem first_three_is_literal_minor (B : Matrix (Fin 3) (Fin 4) R) :
    B.submatrix id Fin.castSucc = B.submatrix id (3 : Fin 4).succAbove := by
  ext i j
  fin_cases j <;> rfl

theorem upper_conditions_of_maximal_permanents (B : Matrix (Fin 3) (Fin 4) R)
    (h : ∀ c : Fin 4, (B.submatrix id c.succAbove).permanent = 0) :
    (B.submatrix id Fin.castSucc).permanent = 0 ∧
    ∀ c : Fin 3, (ComponentFamilyContainment.augmented
      ((B.submatrix id Fin.castSucc).submatrix id c.succAbove) (fun i => B i 3)).permanent = 0 := by
  constructor
  · rw [first_three_is_literal_minor]; exact h 3
  · intro c
    rw [augmented_is_literal_minor]
    exact h c.castSucc

#print axioms upper_conditions_of_maximal_permanents
end ComponentLiteralUpper
