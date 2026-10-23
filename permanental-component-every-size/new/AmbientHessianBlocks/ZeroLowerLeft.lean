import AmbientHessianBlocks.Definitions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ComponentAmbientHessian
noncomputable section
open MvPolynomial Matrix Equiv ComponentChartJacobian

def zeroLEntry (k : ℕ) : Variables k → P k
  | Sum.inl b => X (bVar b)
  | Sum.inr (Sum.inl w) => X (wVar w)
  | Sum.inr (Sum.inr (Sum.inl _)) => 0
  | Sum.inr (Sum.inr (Sum.inr v)) => X (vVar v)

def killL (k : ℕ) : P k →ₐ[ℂ] P k := aeval (zeroLEntry k)

def NonLower {k : ℕ} (x : Variables k) : Prop := ∀ a, lVar a ≠ x

theorem derivative_zeroLEntry {k : ℕ} (x : Variables k) (hx : NonLower x) (a : Variables k) :
    pderiv x (zeroLEntry k a) = if a = x then 1 else 0 := by
  classical
  rcases a with b | (w | (l | v))
  · simp [zeroLEntry, bVar, pderiv_X, Pi.single_apply]
  · simp [zeroLEntry, wVar, pderiv_X, Pi.single_apply]
  · simp [zeroLEntry, show Sum.inr (Sum.inr (Sum.inl l)) ≠ x from hx l]
  · simp [zeroLEntry, vVar, pderiv_X, Pi.single_apply]

theorem pderiv_killL {k : ℕ} (x : Variables k) (hx : NonLower x) (p : P k) :
    pderiv x (killL k p) = killL k (pderiv x p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [killL]
  | add p q hp hq => simp [hp, hq]
  | mul_X p a hp =>
    simp only [killL] at hp
    simp only [map_mul, killL, aeval_X, pderiv_mul, hp, pderiv_X, Pi.single_apply,
      derivative_zeroLEntry x hx, map_add]
    split_ifs <;> simp

theorem eval_killL (k : ℕ) (p : P k) : eval (seed k) (killL k p) = eval (seed k) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [killL]
  | add p q hp hq => simp [hp, hq]
  | mul_X p a hp =>
    simp only [map_mul, hp]
    congr 1
    rcases a with b | (w | (l | v)) <;>
      simp [killL, zeroLEntry, seed, bVar, wVar, lVar, vVar]

theorem killL_actualPolynomial (k : ℕ) : killL k (actualPolynomial k) =
    (blockU k).permanent * (blockW k).permanent := by
  unfold actualPolynomial
  have hmap := ComponentFamilyContainment.permanent_map (killL k).toRingHom (actualAmbient k)
  change ((actualAmbient k).map (killL k)).permanent = killL k (actualAmbient k).permanent at hmap
  rw [← hmap]
  have hm : (actualAmbient k).map (killL k) =
      Matrix.fromBlocks (blockU k) (blockV k) 0 (blockW k) := by
    apply Matrix.ext
    intro a b
    rcases a with a | a <;> rcases b with b | b
    · simp [actualAmbient_blocks, blockU, blockB, Matrix.submatrix, killL, zeroLEntry, bVar]
    · refine Fin.cases ?_ (fun j => ?_) b <;>
        simp [actualAmbient_blocks, blockV, killL, zeroLEntry, bVar, vVar]
    · simp [actualAmbient_blocks, blockL, killL, zeroLEntry, lVar]
    · simp [actualAmbient_blocks, blockW, killL, zeroLEntry, wVar]
  rw [hm, ComponentBlockPermanent.permanent_fromBlocks_zero_lower]

/-- Every Hessian entry in directions outside L is computed by the exact
block-triangular permanent product, before specializing to the seed. -/
theorem hessian_nonLower {k : ℕ} (x y : Variables k) (hx : NonLower x) (hy : NonLower y) :
    hessian k x y = eval (seed k) (pderiv y (pderiv x
      ((blockU k).permanent * (blockW k).permanent))) := by
  unfold hessian
  rw [← eval_killL k (pderiv y (pderiv x (actualPolynomial k))),
    ← pderiv_killL y hy, ← pderiv_killL x hx, killL_actualPolynomial]

#print axioms killL_actualPolynomial
#print axioms hessian_nonLower
end
end ComponentAmbientHessian
