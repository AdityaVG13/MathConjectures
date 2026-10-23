import AmbientPairing.SelectedPairing
import SparseSeed.CofactorDet
import SparseSeed.CofactorVector

namespace AmbientPairing
open Matrix Finset
set_option backward.isDefEq.respectTransparency false

theorem finCofactorMatrix_reindex (k : ℕ) :
    finCofactorMatrix k = (SparseSeed.cofactorMatrix k).submatrix
      (finSuccEquiv k) (finSuccEquiv k) := by
  ext i j
  exact SparseSeed.fin_cofactor_eq k i j

theorem det_finCofactorMatrix (k : ℕ) : (finCofactorMatrix k).det = (-2 : ℂ)^k := by
  rw [finCofactorMatrix_reindex]
  change (Matrix.reindex (finSuccEquiv k).symm (finSuccEquiv k).symm
    (SparseSeed.cofactorMatrix k)).det = _
  rw [Matrix.det_reindex_self, SparseSeed.det_cofactorMatrix]

theorem det_finCofactorMatrix_ne_zero (k : ℕ) : (finCofactorMatrix k).det ≠ 0 := by
  rw [det_finCofactorMatrix]
  exact pow_ne_zero _ (by norm_num)

theorem seedLambda_reindex (k : ℕ) (j : Fin (k+1)) :
    seedLambda k j = SparseSeed.lambda k (finSuccEquiv k j) := by
  refine Fin.cases ?_ (fun j => ?_) j <;> simp [seedLambda, SparseSeed.lambda]

theorem finCofactor_mul_lambda (k : ℕ) (a : Fin (k+1)) :
    (finCofactorMatrix k).mulVec (seedLambda k) a =
      (SparseSeed.cofactorMatrix k).mulVec (SparseSeed.lambda k) (finSuccEquiv k a) := by
  simp only [Matrix.mulVec, dotProduct]
  apply Fintype.sum_equiv (finSuccEquiv k)
  intro j
  rw [seedLambda_reindex]
  congr 1
  exact SparseSeed.fin_cofactor_eq k a j

end AmbientPairing
#print axioms AmbientPairing.det_finCofactorMatrix_ne_zero
#print axioms AmbientPairing.finCofactor_mul_lambda
