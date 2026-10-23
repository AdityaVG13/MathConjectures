import UpperSeed.UpperSeed

set_option autoImplicit false
namespace ComponentUpperPairing
open ComponentUpperSeed Matrix

theorem annihilator_complement (row : Fin 3 → ℂ)
    (h : ∀ w : Fin 3 → ℂ, w 0 = 0 → dotProduct row (T.mulVec w) = 0) :
    row = (row 0 / 1034) • k := by
  have h1 := h ![0,1,0] (by rfl)
  have h2 := h ![0,0,1] (by rfl)
  norm_num [T, permanent_two, U, B, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove] at h1 h2
  ext i
  fin_cases i
  · simp [k]
  · simp only [Pi.smul_apply, smul_eq_mul]
    norm_num [k]
    linear_combination (312/329 : ℂ)*h1+(117/3619 : ℂ)*h2
  · simp only [Pi.smul_apply, smul_eq_mul]
    norm_num [k]
    linear_combination (363/658 : ℂ)*h1+(765/1316 : ℂ)*h2

theorem annihilator_rows (l : ℕ) (lam : Option (Fin l) → ℂ) (hlam : lam none = 1)
    (L : Option (Fin l) → Fin 3 → ℂ)
    (hw : ∀ j : Fin l, ∀ w : Fin 3 → ℂ, w 0 = 0 →
      dotProduct (L (some j)) (T.mulVec w) = 0)
    (hc : ∑ j : Option (Fin l), lam j • L j = 0) :
    ∃ z : Option (Fin l) → ℂ,
      (∀ j, L j = z j • k) ∧ (∑ j, lam j*z j) = 0 := by
  let zs : Fin l → ℂ := fun j => L (some j) 0 / 1034
  have hs (j : Fin l) : L (some j) = zs j • k := annihilator_complement _ (hw j)
  let z : Option (Fin l) → ℂ := fun j =>
    match j with
    | none => -(∑ a : Fin l, lam (some a)*zs a)
    | some a => zs a
  refine ⟨z, ?_, ?_⟩
  · intro j
    cases j with
    | some j => exact hs j
    | none =>
      funext i
      have hi := congrFun hc i
      simp only [Fintype.sum_option, hlam, one_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      have he : (∑ j : Fin l, lam (some j)*L (some j) i) =
          (∑ j : Fin l, lam (some j)*zs j)*k i := by
        simp only [hs, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [he] at hi
      change L none i = (-(∑ a : Fin l, lam (some a)*zs a))*k i
      linear_combination hi
  · simp [z, Fintype.sum_option, hlam]

#print axioms annihilator_rows
#print axioms annihilator_complement
end ComponentUpperPairing
