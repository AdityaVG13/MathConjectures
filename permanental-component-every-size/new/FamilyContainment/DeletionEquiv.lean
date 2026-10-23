import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic
namespace ComponentFamilyContainment
/-- Delete precisely one right-summand index, keeping every left index. -/
def deleteRight {α : Type*} {n : ℕ} (i : Fin (n+1)) :
    (α ⊕ Fin n) ≃ {x : α ⊕ Fin (n+1) // x ≠ Sum.inr i} where
  toFun x := match x with
    | Sum.inl a => ⟨Sum.inl a, by simp⟩
    | Sum.inr b => ⟨Sum.inr (i.succAbove b), by simp⟩
  invFun x := match x with
    | ⟨Sum.inl a, _⟩ => Sum.inl a
    | ⟨Sum.inr b, h⟩ => Sum.inr ((finSuccAboveEquiv i).symm ⟨b, by simpa using h⟩)
  left_inv x := by
    cases x with
    | inl a => rfl
    | inr b => exact congrArg Sum.inr ((finSuccAboveEquiv i).symm_apply_apply b)
  right_inv x := by
    rcases x with ⟨a | b, h⟩
    · rfl
    · apply Subtype.ext
      change Sum.inr (i.succAbove ((finSuccAboveEquiv i).symm ⟨b, _⟩)) = Sum.inr b
      exact congrArg (fun x : {x // x ≠ i} => Sum.inr x.val)
        ((finSuccAboveEquiv i).apply_symm_apply ⟨b, by simpa using h⟩)

@[simp] theorem deleteRight_val {α : Type*} {n : ℕ} (i : Fin (n+1))
    (x : α ⊕ Fin n) : (deleteRight i x).val = Sum.map id i.succAbove x := by
  cases x <;> rfl

/-- Delete precisely one left-summand index, keeping every right index. -/
def deleteLeft {α : Type*} {n : ℕ} (i : Fin (n+1)) :
    (Fin n ⊕ α) ≃ {x : Fin (n+1) ⊕ α // x ≠ Sum.inl i} :=
  (Equiv.sumComm _ _).trans ((deleteRight i).trans
    ((Equiv.sumComm _ _).subtypeEquiv (by intro x; cases x <;> simp)))

@[simp] theorem deleteLeft_val {α : Type*} {n : ℕ} (i : Fin (n+1))
    (x : Fin n ⊕ α) : (deleteLeft i x).val = Sum.map i.succAbove id x := by
  cases x <;> rfl

end ComponentFamilyContainment
