import AmbientPairing.ActualPairing

set_option autoImplicit false
namespace ComponentActualLocalChart
noncomputable section
open MvPolynomial Matrix ComponentChartJacobian ComponentAmbientHessian

def actualDeterminant (k : ℕ) : P k := (actualAmbient k).det

theorem determinant_seed (k : ℕ) :
    eval (seed k) (actualDeterminant k) = (46718/3861 : ℂ)*(k:ℂ) := by
  unfold actualDeterminant
  rw [RingHom.map_det]
  change ((actualAmbient k).map (eval (seed k))).det = _
  have hm : (actualAmbient k).map (eval (seed k)) =
      Matrix.fromBlocks ComponentUpperSeed.U (AmbientPairing.seedRight k) 0 (SparseSeed.finArrowhead k) := by
    rw [← AmbientPairing.seed_matrix]
    ext i j
    simp [actualAmbient, Matrix.map_apply]
  rw [hm, Matrix.det_fromBlocks_zero₂₁, ComponentUpperSeed.upper_det]
  have hw : (SparseSeed.finArrowhead k).det = -2*(k:ℂ) := by
    rw [SparseSeed.finArrowhead, Matrix.det_submatrix_equiv_self, SparseSeed.det_arrowhead]
  rw [hw]
  ring

theorem determinant_seed_ne_zero (k : ℕ) (hk : 1 ≤ k) :
    eval (seed k) (actualDeterminant k) ≠ 0 := by
  rw [determinant_seed]
  apply mul_ne_zero (by norm_num)
  exact_mod_cast (show k ≠ 0 by omega)

#print axioms determinant_seed_ne_zero
end
end ComponentActualLocalChart
