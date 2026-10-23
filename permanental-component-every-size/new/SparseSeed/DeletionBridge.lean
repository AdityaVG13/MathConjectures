import SparseSeed.Cofactors
import Mathlib.GroupTheory.Perm.Option
import Mathlib.Logic.Equiv.Fin.Basic

namespace SparseSeed

/-- The same lower seed in conventional zero-based finite indexing. -/
def finArrowhead (l : ℕ) : Matrix (Fin (l + 1)) (Fin (l + 1)) ℂ :=
  (arrowhead l).submatrix (finSuccEquiv l) (finSuccEquiv l)

/-- Coordinate change between increasing-order deletion and swap-based deletion. -/
private def deletionPerm (l : ℕ) (a : Fin (l + 1)) : Equiv.Perm (Fin l) :=
  Equiv.removeNone (((finSuccEquiv' a).symm.trans (finSuccEquiv l)).trans
    (Equiv.swap none (finSuccEquiv l a)))

private theorem deletionPerm_spec (l : ℕ) (a : Fin (l + 1)) (i : Fin l) :
    Equiv.swap none (finSuccEquiv l a) (some (deletionPerm l a i)) =
      finSuccEquiv l (a.succAbove i) := by
  let r : Equiv.Perm (Option (Fin l)) :=
    ((finSuccEquiv' a).symm.trans (finSuccEquiv l)).trans
      (Equiv.swap none (finSuccEquiv l a))
  have hr : r none = none := by simp [r]
  have he : (Equiv.removeNone r).optionCongr = r := by
    calc
      (Equiv.removeNone r).optionCongr = Equiv.swap none (r none) * r := map_equiv_removeNone r
      _ = r := by rw [hr, Equiv.swap_self]; rfl
  have hi := congrArg (fun σ : Equiv.Perm (Option (Fin l)) => σ (some i)) he
  have hi' : some (deletionPerm l a i) =
      Equiv.swap none (finSuccEquiv l a) (finSuccEquiv l (a.succAbove i)) := by
    change some (Equiv.removeNone r i) = r (some i) at hi
    simpa only [r, deletionPerm, Equiv.trans_apply, finSuccEquiv'_symm_some] using hi
  rw [hi', Equiv.swap_apply_self]

/-- The computed cofactors are precisely the standard `Fin.succAbove` permanent minors. -/
theorem fin_cofactor_eq (l : ℕ) (a b : Fin (l + 1)) :
    ((finArrowhead l).submatrix a.succAbove b.succAbove).permanent =
      cofactor l (finSuccEquiv l a) (finSuccEquiv l b) := by
  let N := (arrowhead l).submatrix
    (fun i => Equiv.swap none (finSuccEquiv l a) (some i))
    (fun j => Equiv.swap none (finSuccEquiv l b) (some j))
  have he : (finArrowhead l).submatrix a.succAbove b.succAbove =
      N.submatrix (deletionPerm l a) (deletionPerm l b) := by
    ext i j
    change arrowhead l (finSuccEquiv l (a.succAbove i)) (finSuccEquiv l (b.succAbove j)) =
      arrowhead l (Equiv.swap none (finSuccEquiv l a) (some (deletionPerm l a i)))
        (Equiv.swap none (finSuccEquiv l b) (some (deletionPerm l b j)))
    rw [deletionPerm_spec, deletionPerm_spec]
  rw [he]
  change (N.submatrix (deletionPerm l a) (deletionPerm l b)).permanent = N.permanent
  have he' : N.submatrix (deletionPerm l a) (deletionPerm l b) =
      (N.submatrix (deletionPerm l a) id).submatrix id (deletionPerm l b) := rfl
  rw [he', Matrix.permanent_permute_rows, Matrix.permanent_permute_cols]

end SparseSeed

#print axioms SparseSeed.fin_cofactor_eq
