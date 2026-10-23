import FamilyContainment.AllCofactors

set_option backward.isDefEq.respectTransparency false
namespace ComponentFamilyContainment
open Matrix Equiv
variable {R : Type*} [CommRing R]

theorem cofactor_eq_minor_equiv {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (A : Matrix α α R) (r c : α)
    (er : β ≃ {x : α // x ≠ r}) (ec : β ≃ {x : α // x ≠ c}) :
    cofactor A r c =
      (A.submatrix (fun i => (er i).val) (fun j => (ec j).val)).permanent := by
  unfold cofactor
  rw [← ComponentGeneralLaplace.permanent_reindex_independent er
    (ec.trans (ComponentGeneralLaplace.swapComplement r c).symm)]
  congr 1
  ext i j
  simp [Matrix.submatrix, ComponentGeneralLaplace.swapComplement]

/-- The subtype cofactor is exactly the usual Fin.succAbove minor, after
any simultaneous row/column equivalence. -/
theorem cofactor_reindex_fin {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (A : Matrix α α R) (e : Fin (n+1) ≃ α) (r c : Fin (n+1)) :
    cofactor A (e r) (e c) =
      ((A.submatrix e e).submatrix r.succAbove c.succAbove).permanent := by
  let er : Fin n ≃ {x : α // x ≠ e r} := (finSuccAboveEquiv r).trans
    (e.subtypeEquiv (by intro x; exact e.injective.ne_iff.symm))
  let ec : Fin n ≃ {x : α // x ≠ e c} := (finSuccAboveEquiv c).trans
    (e.subtypeEquiv (by intro x; exact e.injective.ne_iff.symm))
  rw [cofactor_eq_minor_equiv A (e r) (e c) er ec]
  rfl

def familyIndexEquiv (k : ℕ) : Fin (3+k+1) ≃ (Fin 3 ⊕ Fin (k+1)) :=
  (finCongr (by omega) : Fin (3+k+1) ≃ Fin (3+(k+1))).trans finSumFinEquiv.symm

/-- The full family in the conventional Fin(n) ordering, top indices first. -/
def familyFin {k : ℕ} (U : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R)
    (lam : Fin (k+1) → R) (W : Matrix (Fin (k+1)) (Fin (k+1)) R) :
    Matrix (Fin (3+k+1)) (Fin (3+k+1)) R :=
  (family U v lam W).submatrix (familyIndexEquiv k) (familyIndexEquiv k)

/-- Actual conventional submaximal permanental equations vanish uniformly. -/
theorem all_fin_cofactors_zero {k : ℕ} (U : Matrix (Fin 3) (Fin 3) R)
    (v : Fin 3 → R) (lam : Fin (k+1) → R)
    (W : Matrix (Fin (k+1)) (Fin (k+1)) R)
    (hW : W.permanent = 0) (hU : U.permanent = 0)
    (hB : ∀ j : Fin 3, (augmented (U.submatrix id j.succAbove) v).permanent = 0)
    (r c : Fin (3+k+1)) :
    ((familyFin U v lam W).submatrix r.succAbove c.succAbove).permanent = 0 := by
  unfold familyFin
  rw [← cofactor_reindex_fin (family U v lam W) (familyIndexEquiv k) r c]
  exact all_cofactors_zero U v lam W hW hU hB _ _

#print axioms all_fin_cofactors_zero
end ComponentFamilyContainment
