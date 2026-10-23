import FamilyContainment.BottomLeft
import FamilyContainment.TopRight

set_option backward.isDefEq.respectTransparency false
namespace ComponentFamilyContainment
open Matrix Equiv
variable {R : Type*} [CommRing R]

/-- A genuine unsigned cofactor: the row is deleted by its complement subtype,
and the column by the canonical swap bijection. -/
def cofactor {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α R) (r c : α) : R :=
  (A.submatrix (fun x : {x : α // x ≠ r} => x.val)
    (fun x : {x : α // x ≠ r} => Equiv.swap r c x.val)).permanent

theorem cofactor_zero_of_equiv {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (A : Matrix α α R) (r c : α)
    (er : β ≃ {x : α // x ≠ r}) (ec : β ≃ {x : α // x ≠ c})
    (h : (A.submatrix (fun i => (er i).val) (fun j => (ec j).val)).permanent = 0) :
    cofactor A r c = 0 := by
  unfold cofactor
  rw [← ComponentGeneralLaplace.permanent_reindex_independent er
    (ec.trans (ComponentGeneralLaplace.swapComplement r c).symm)]
  convert h using 1
  congr 1
  ext i j
  simp [Matrix.submatrix, ComponentGeneralLaplace.swapComplement]

/-- Every submaximal permanent of the full uniform family vanishes.
There are no full-support, invertibility, characteristic, or seed assumptions. -/
theorem all_cofactors_zero {k : ℕ} (U : Matrix (Fin 3) (Fin 3) R)
    (v : Fin 3 → R) (lam : Fin (k+1) → R)
    (W : Matrix (Fin (k+1)) (Fin (k+1)) R)
    (hW : W.permanent = 0) (hU : U.permanent = 0)
    (hB : ∀ j : Fin 3, (augmented (U.submatrix id j.succAbove) v).permanent = 0)
    (r c : Fin 3 ⊕ Fin (k+1)) :
    cofactor (family U v lam W) r c = 0 := by
  classical
  cases r with
  | inl i =>
    cases c with
    | inl j =>
      apply cofactor_zero_of_equiv _ _ _ (deleteLeft i) (deleteLeft j)
      convert top_left_minor_zero U v lam W hW i j using 1
      congr 1
      ext a b
      rw [Matrix.submatrix_apply, deleteLeft_val, deleteLeft_val]
      rfl
    | inr j =>
      let e : (Fin 2 ⊕ Fin (k+1)) ≃ (Fin 3 ⊕ Fin k) :=
        Fintype.equivOfCardEq (by simp; omega)
      apply cofactor_zero_of_equiv _ _ _ (deleteLeft i) (e.trans (deleteRight j))
      convert top_right_minor_zero U v lam W i j e using 1
      congr 1
      ext a b
      change family U v lam W (deleteLeft i a).val (deleteRight j (e b)).val = _
      rw [deleteLeft_val, deleteRight_val]
      rfl
  | inr i =>
    cases c with
    | inl j =>
      let e : (Fin 3 ⊕ Fin k) ≃ (Fin 2 ⊕ Fin (k+1)) :=
        Fintype.equivOfCardEq (by simp; omega)
      apply cofactor_zero_of_equiv _ _ _ (deleteRight i) (e.trans (deleteLeft j))
      convert bottom_left_minor_zero U v lam W i j (hB j) e using 1
      congr 1
      ext a b
      change family U v lam W (deleteRight i a).val (deleteLeft j (e b)).val = _
      rw [deleteRight_val, deleteLeft_val]
      rfl
    | inr j =>
      apply cofactor_zero_of_equiv _ _ _ (deleteRight i) (deleteRight j)
      convert bottom_right_minor_zero U v lam W hU i j using 1
      congr 1
      ext a b
      rw [Matrix.submatrix_apply, deleteRight_val, deleteRight_val]
      rfl

#print axioms all_cofactors_zero
end ComponentFamilyContainment
