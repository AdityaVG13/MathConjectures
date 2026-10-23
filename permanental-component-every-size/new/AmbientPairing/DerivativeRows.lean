import SparseSeed.RowDerivative

namespace AmbientPairing
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
variable {n t : Type*} [Fintype n] [DecidableEq n] [DecidableEq t]

/-- Differentiating two distinct rows of a generic permanent replaces them with coordinate rows. -/
theorem eval_generic_mixed_rows (e : t ≃ n × n) (z : t → ℂ) (x y : t)
    (hxy : (e x).1 ≠ (e y).1) :
    eval z (pderiv y (pderiv x (Matrix.permanent (fun i j => (X (e.symm (i,j)) : MvPolynomial t ℂ))))) =
      (Matrix.updateRow (Matrix.updateRow (fun i j => z (e.symm (i,j))) (e x).1
        (fun j => if j = (e x).2 then 1 else 0)) (e y).1
        (fun j => if j = (e y).2 then 1 else 0)).permanent := by
  let M : Matrix n n (MvPolynomial t ℂ) := fun i j => X (e.symm (i,j))
  let D (v : t) (j : n) : MvPolynomial t ℂ := if j = (e v).2 then 1 else 0
  have hd (v : t) (i j : n) : pderiv v (M i j) = if i = (e v).1 then D v j else 0 := by
    have he : e.symm (i,j) = v ↔ i = (e v).1 ∧ j = (e v).2 := by
      constructor
      · intro h
        have hh := congrArg e h
        simp only [Equiv.apply_symm_apply] at hh
        exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩
      · rintro ⟨hi,hj⟩
        rw [hi,hj, Prod.mk.eta, Equiv.symm_apply_apply]
    simp only [M, pderiv_X, Pi.single_apply]
    simp only [he]
    by_cases hi : i = (e v).1 <;> by_cases hj : j = (e v).2 <;>
      simp [D, hi, hj]
  change eval z (pderiv y (pderiv x M.permanent)) = _
  rw [SparseSeed.pderiv_permanent_row x M (e x).1 (D x) (hd x)]
  rw [SparseSeed.pderiv_permanent_row y _ (e y).1 (D y)]
  · rw [SparseSeed.eval_permanent]
    congr 1
    ext i j
    by_cases hx : i = (e x).1 <;> by_cases hy : i = (e y).1 <;>
      by_cases hjx : j = (e x).2 <;> by_cases hjy : j = (e y).2 <;>
      simp_all [Matrix.updateRow_apply, M, D]
  · intro i j
    by_cases hx : i = (e x).1
    · subst i
      by_cases hj : j = (e x).2 <;> simp [D, hxy, hj]
    · rw [Matrix.updateRow_ne hx, hd]

end AmbientPairing
#print axioms AmbientPairing.eval_generic_mixed_rows
