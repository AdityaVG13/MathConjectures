import FamilyContainment.DeletionEquiv
import GeneralLaplace.GeneralLaplace
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false
namespace ComponentFamilyContainment
open Matrix Equiv
variable {R : Type*} [CommRing R]

def crossing {m : ℕ} (U : Matrix (Fin 3) (Fin 2) R) (v : Fin 3 → R)
    (lam : Fin (m+1) → R) (W : Matrix (Fin m) (Fin (m+1)) R) :
    Matrix (Fin 3 ⊕ Fin m) (Fin 2 ⊕ Fin (m+1)) R :=
  Matrix.fromBlocks U (fun i j => v i * lam j) 0 W

/-- Removing all lower rows by Laplace expansion leaves exactly two left
columns and one proportional right column. This statement is uniform in m. -/
theorem crossing_zero (U : Matrix (Fin 3) (Fin 2) R) (v : Fin 3 → R)
    (hbase : ∀ (t : R) (e : Fin 3 ≃ (Fin 2 ⊕ Fin 1)),
      (Matrix.of (fun i j => Sum.elim (U i) (fun _ => v i * t) (e j))).permanent = 0) :
    ∀ (m : ℕ) (lam : Fin (m+1) → R) (W : Matrix (Fin m) (Fin (m+1)) R)
      (e : (Fin 3 ⊕ Fin m) ≃ (Fin 2 ⊕ Fin (m+1))),
      ((crossing U v lam W).submatrix id e).permanent = 0 := by
  intro m
  induction m with
  | zero =>
    intro lam W e
    let er : Fin 3 ≃ (Fin 3 ⊕ Fin 0) := (Equiv.sumEmpty (Fin 3) (Fin 0)).symm
    rw [← ComponentGeneralLaplace.permanent_reindex er]
    convert hbase (lam 0) (er.trans e) using 1
    congr 1
    ext i j
    change crossing U v lam W (Sum.inl i) (e (er j)) =
      Sum.elim (U i) (fun _ => v i * lam 0) (e (er j))
    cases hh : e (er j) with
    | inl a => rfl
    | inr b =>
      have hb : b = 0 := Fin.ext (by omega)
      subst b
      rfl
  | succ m ih =>
    intro lam W e
    let r : Fin 3 ⊕ Fin (m+1) := Sum.inr (Fin.last m)
    apply ComponentGeneralLaplace.zero_of_row_minors_equiv (β := Fin 3 ⊕ Fin m)
      ((crossing U v lam W).submatrix id e) r
    intro c hc
    have hright : ∃ q, e c = Sum.inr q := by
      cases hh : e c with
      | inl a => exact False.elim (hc (by simp [Matrix.submatrix, crossing, r, hh]))
      | inr q => exact ⟨q, rfl⟩
    obtain ⟨q, hq⟩ := hright
    let en : (Fin 3 ⊕ Fin m) ≃ (Fin 2 ⊕ Fin (m+1)) :=
      Fintype.equivOfCardEq (by simp; omega)
    let er : (Fin 3 ⊕ Fin m) ≃ {x : Fin 3 ⊕ Fin (m+1) // x ≠ r} :=
      deleteRight (Fin.last m)
    let ec0 : {x : Fin 2 ⊕ Fin (m+2) // x ≠ Sum.inr q} ≃
        {x : Fin 3 ⊕ Fin (m+1) // x ≠ c} :=
      e.symm.subtypeEquiv (by intro x; rw [← hq]; simpa using (e.symm.injective.ne_iff (x := x) (y := e c)).symm)
    let ec := en.trans ((deleteRight q).trans ec0)
    refine ⟨er, ec, ?_⟩
    convert ih (fun j => lam (q.succAbove j))
      (W.submatrix (Fin.last m).succAbove q.succAbove) en using 1
    congr 1
    ext a b
    change crossing U v lam W (er a).val (e (ec b).val) = _
    have hec : e (ec b).val = Sum.map id q.succAbove (en b) := by
      simp [ec, ec0, Equiv.trans_apply, deleteRight_val]
    rw [hec]
    have her : (er a).val = Sum.map id (Fin.last m).succAbove a := deleteRight_val _ _
    rw [her]
    change crossing U v lam W (Sum.map id (Fin.last m).succAbove a)
      (Sum.map id q.succAbove (en b)) =
      crossing U v (fun j => lam (q.succAbove j))
        (W.submatrix (Fin.last m).succAbove q.succAbove) a (en b)
    cases a <;> cases he : en b <;> rfl

#print axioms crossing_zero
end ComponentFamilyContainment
