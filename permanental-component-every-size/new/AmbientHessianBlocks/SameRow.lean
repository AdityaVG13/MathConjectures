import AmbientHessianBlocks.Definitions
import SparseSeed.RowDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ComponentAmbientHessian
noncomputable section
open MvPolynomial Matrix Equiv ComponentChartJacobian

/-- The actual generic permanent is affine in each row, hence all second
partials involving two entries in the same row vanish identically. -/
theorem generic_second_same_row {n t : Type*} [Fintype n] [DecidableEq n] [DecidableEq t]
    (e : t ≃ n × n) (x y : t) (hxy : (e x).1 = (e y).1) :
    pderiv y (pderiv x (Matrix.permanent
      (fun i j => (X (e.symm (i,j)) : MvPolynomial t ℂ)))) = 0 := by
  let M : Matrix n n (MvPolynomial t ℂ) := fun i j => X (e.symm (i,j))
  let D (j : n) : MvPolynomial t ℂ := if j = (e x).2 then 1 else 0
  have hd (i j : n) : pderiv x (M i j) = if i = (e x).1 then D j else 0 := by
    have he : e.symm (i,j) = x ↔ i = (e x).1 ∧ j = (e x).2 := by
      constructor
      · intro h
        have hh := congrArg e h
        simp only [Equiv.apply_symm_apply] at hh
        exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩
      · rintro ⟨hi,hj⟩
        rw [hi,hj, Prod.mk.eta, Equiv.symm_apply_apply]
    simp only [M, pderiv_X, Pi.single_apply, he]
    by_cases hi : i = (e x).1 <;> by_cases hj : j = (e x).2 <;> simp [D,hi,hj]
  change pderiv y (pderiv x M.permanent) = 0
  rw [SparseSeed.pderiv_permanent_row x M (e x).1 D hd]
  apply SparseSeed.pderiv_permanent_zero
  intro i j
  by_cases hi : i = (e x).1
  · subst i
    by_cases hj : j = (e x).2 <;> simp [D,hj]
  · rw [Matrix.updateRow_ne hi]
    have hn : e.symm (i,j) ≠ y := by
      intro hh
      have hrow := congrArg (fun z => (e z).1) hh
      simp only [Equiv.apply_symm_apply] at hrow
      exact hi (hrow.trans hxy.symm)
    simp [M, pderiv_X, Pi.single_apply, hn]

theorem hessian_same_row (k : ℕ) (x y : Variables k)
    (hxy : (entryEquiv k x).1 = (entryEquiv k y).1) : hessian k x y = 0 := by
  unfold hessian actualPolynomial actualAmbient
  rw [generic_second_same_row (entryEquiv k) x y hxy, map_zero]

#print axioms hessian_same_row
end
end ComponentAmbientHessian
