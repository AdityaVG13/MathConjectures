import UpperSeed.UpperSeed
import SparseSeed.DeletionBridge
import FamilyContainment.IdealContainment
import ExceptionalCofactorDerivative
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ComponentChartJacobian
noncomputable section
open MvPolynomial Matrix Equiv

abbrev BIndex := Fin 3 × Fin 4
abbrev WIndex (k : ℕ) := Fin (k+1) × Fin (k+1)
abbrev LIndex (k : ℕ) := Fin (k+1) × Fin 3
abbrev VIndex (k : ℕ) := Fin 3 × Fin k
abbrev Variables (k : ℕ) := BIndex ⊕ (WIndex k ⊕ (LIndex k ⊕ VIndex k))
abbrev P (k : ℕ) := MvPolynomial (Variables k) ℂ
abbrev Rest (k : ℕ) := Unit ⊕ (LIndex k ⊕ (Fin 2 × Fin k))
abbrev Generators (k : ℕ) := Fin 4 ⊕ Rest k

def bVar {k : ℕ} (x : BIndex) : Variables k := Sum.inl x
def wVar {k : ℕ} (x : WIndex k) : Variables k := Sum.inr (Sum.inl x)
def lVar {k : ℕ} (x : LIndex k) : Variables k := Sum.inr (Sum.inr (Sum.inl x))
def vVar {k : ℕ} (x : VIndex k) : Variables k := Sum.inr (Sum.inr (Sum.inr x))

def genericW (k : ℕ) : Matrix (Fin (k+1)) (Fin (k+1)) (MvPolynomial (WIndex k) ℂ) :=
  fun i j => X (i,j)

def upperPolynomial (k : ℕ) (c : Fin 4) : P k :=
  rename bVar ((ComponentUpperSeed.genericB.submatrix id c.succAbove).permanent)

def lowerPolynomial (k : ℕ) : P k := rename wVar (genericW k).permanent

def proportionality (k : ℕ) (ij : Fin 2 × Fin k) : P k :=
  X (bVar (0,3)) * X (vVar (ij.1.succ,ij.2)) -
    X (bVar (ij.1.succ,3)) * X (vVar (0,ij.2))

def generator (k : ℕ) : Generators k → P k
  | Sum.inl c => upperPolynomial k c
  | Sum.inr (Sum.inl _) => lowerPolynomial k
  | Sum.inr (Sum.inr (Sum.inl ac)) => X (lVar ac)
  | Sum.inr (Sum.inr (Sum.inr ij)) => proportionality k ij

def selected (k : ℕ) : Generators k → Variables k
  | Sum.inl c => bVar (ComponentUpperSeed.selected c)
  | Sum.inr (Sum.inl _) => wVar (0,0)
  | Sum.inr (Sum.inr (Sum.inl ac)) => lVar ac
  | Sum.inr (Sum.inr (Sum.inr ij)) => vVar (ij.1.succ,ij.2)

def seed (k : ℕ) : Variables k → ℂ
  | Sum.inl ij => ComponentUpperSeed.B ij.1 ij.2
  | Sum.inr (Sum.inl ij) => SparseSeed.finArrowhead k ij.1 ij.2
  | Sum.inr (Sum.inr (Sum.inl _)) => 0
  | Sum.inr (Sum.inr (Sum.inr ij)) => 2 * ComponentUpperSeed.v ij.1

def jacobian (k : ℕ) : Matrix (Generators k) (Generators k) ℂ :=
  fun r c => eval (seed k) (pderiv (selected k c) (generator k r))

theorem pderiv_rename_outside {α β : Type*} (f : α → β) (j : β)
    (h : ∀ i, f i ≠ j) (p : MvPolynomial α ℂ) :
    pderiv j (rename f p) = 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [pderiv_mul, hp, pderiv_X, Pi.single_apply, h i]

theorem upper_upper (k : ℕ) (r c : Fin 4) :
    jacobian k (Sum.inl r) (Sum.inl c) = ComponentUpperSeed.jac r c := by
  change eval (seed k) (pderiv (bVar (ComponentUpperSeed.selected c))
    (rename bVar ((ComponentUpperSeed.genericB.submatrix id r.succAbove).permanent))) = _
  rw [pderiv_rename (show Function.Injective (bVar (k := k)) from Sum.inl_injective), eval_rename]
  rfl

theorem lower_lower (k : ℕ) :
    jacobian k (Sum.inr (Sum.inl ())) (Sum.inr (Sum.inl ())) = 1 := by
  change eval (seed k) (pderiv (wVar (0,0)) (rename wVar (genericW k).permanent)) = 1
  have hinj : Function.Injective (wVar (k := k)) := fun _ _ h => Sum.inl.inj (Sum.inr.inj h)
  rw [pderiv_rename hinj, eval_rename]
  have hd : pderiv (0,0) (genericW k).permanent =
      ((genericW k).submatrix (0 : Fin (k+1)).succAbove (0 : Fin (k+1)).succAbove).permanent := by
    convert ExceptionalCofactorDerivative.permanent_derivative_single (0,0) (genericW k) 0 0 1 ?_ using 1
    · simp
    · intro r c
      simp [genericW, pderiv_X, Pi.single_apply, Prod.mk.injEq, eq_comm]
  rw [hd, ← ComponentFamilyContainment.permanent_map (eval (seed k ∘ wVar))]
  have he : (((genericW k).submatrix (0 : Fin (k+1)).succAbove
      (0 : Fin (k+1)).succAbove).map (eval (seed k ∘ wVar))) =
      (SparseSeed.finArrowhead k).submatrix (0 : Fin (k+1)).succAbove
      (0 : Fin (k+1)).succAbove := by
    ext i j
    simp [genericW, Matrix.submatrix, seed, wVar]
  rw [he]
  rw [SparseSeed.fin_cofactor_eq]
  simp


theorem upper_outside (k : ℕ) (r : Fin 4)
    (j : WIndex k ⊕ (LIndex k ⊕ VIndex k)) :
    eval (seed k) (pderiv (Sum.inr j) (upperPolynomial k r)) = 0 := by
  unfold upperPolynomial
  rw [pderiv_rename_outside bVar (Sum.inr j) (by intro x; simp [bVar])]
  simp

theorem lower_outside (k : ℕ) (j : Variables k) (h : ∀ x, wVar x ≠ j) :
    eval (seed k) (pderiv j (lowerPolynomial k)) = 0 := by
  unfold lowerPolynomial
  rw [pderiv_rename_outside wVar j h]
  simp

theorem jacobian_block (k : ℕ) : jacobian k =
    Matrix.fromBlocks ComponentUpperSeed.jac 0 0 (1 : Matrix (Rest k) (Rest k) ℂ) := by
  ext r c
  rcases r with r | (_ | (r | r)) <;> rcases c with c | (_ | (c | c))
  · exact upper_upper k r c
  · exact upper_outside k r (Sum.inl (0,0))
  · exact upper_outside k r (Sum.inr (Sum.inl c))
  · exact upper_outside k r (Sum.inr (Sum.inr (c.1.succ,c.2)))
  · apply lower_outside
    intro x
    simp [wVar, bVar, selected]
  · simpa using lower_lower k
  · apply lower_outside
    intro x
    simp [wVar, lVar, selected]
  · apply lower_outside
    intro x
    simp [wVar, vVar, selected]
  · simp [jacobian, selected, generator, lVar, bVar, pderiv_X]
  · simp [jacobian, selected, generator, lVar, wVar, pderiv_X]
  · simp [jacobian, selected, generator, lVar, pderiv_X, Pi.single_apply, Matrix.one_apply]
  · simp [jacobian, selected, generator, lVar, vVar, pderiv_X]
  · fin_cases c <;> simp [jacobian, selected, generator, proportionality, bVar, vVar,
      ComponentUpperSeed.selected, pderiv_X, Pi.single_apply]
  · simp [jacobian, selected, generator, proportionality, bVar, vVar, wVar,
      pderiv_X, Pi.single_apply]
  · simp [jacobian, selected, generator, proportionality, bVar, vVar, lVar,
      pderiv_X, Pi.single_apply]
  · simp [jacobian, selected, generator, proportionality, bVar, vVar,
      pderiv_X, Pi.single_apply, Prod.mk.injEq, seed, ComponentUpperSeed.B,
      Matrix.one_apply, mul_comm]
    by_cases h : r = c
    · subst c
      simp [seed, ComponentUpperSeed.B]
    · have hn : ¬ (r.1 = c.1 ∧ r.2 = c.2) := fun hh => h (Prod.ext hh.1 hh.2)
      simp [hn, h]

theorem jacobian_det (k : ℕ) : (jacobian k).det = -1392580/382239 := by
  rw [jacobian_block, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
    ComponentUpperSeed.jac_det]

theorem jacobian_det_ne_zero (k : ℕ) : (jacobian k).det ≠ 0 := by
  rw [jacobian_det]
  norm_num

theorem generator_count (k : ℕ) : Fintype.card (Generators k) = 5*(k+1)+3 := by
  simp [Generators, Rest, LIndex]
  omega

def fullJacobian (k : ℕ) : Matrix (Generators k) (Variables k) ℂ :=
  fun r x => eval (seed k) (pderiv x (generator k r))

theorem selected_jacobian_rank (k : ℕ) : (jacobian k).rank = 5*(k+1)+3 := by
  rw [Matrix.rank_of_det_ne_zero (jacobian_det_ne_zero k), generator_count]

/-- Rank of the actual rectangular derivative matrix, not a surrogate form. -/
theorem full_jacobian_rank (k : ℕ) : (fullJacobian k).rank = 5*(k+1)+3 := by
  apply le_antisymm
  · have hh := (fullJacobian k).rank_le_card_height
    rw [generator_count] at hh
    exact hh
  · have hh := (fullJacobian k).rank_submatrix_le id (selected k)
    change (jacobian k).rank ≤ (fullJacobian k).rank at hh
    rw [selected_jacobian_rank] at hh
    exact hh

/-- All ambient entries are independent variables, grouped by their blocks. -/
def blockB (k : ℕ) : Matrix (Fin 3) (Fin 4) (P k) := fun i j => X (bVar (i,j))
def blockW (k : ℕ) : Matrix (Fin (k+1)) (Fin (k+1)) (P k) := fun i j => X (wVar (i,j))
def blockL (k : ℕ) : Matrix (Fin (k+1)) (Fin 3) (P k) := fun i j => X (lVar (i,j))
def blockV (k : ℕ) : Matrix (Fin 3) (Fin (k+1)) (P k) :=
  fun i j => Fin.cases (X (bVar (i,3))) (fun t => X (vVar (i,t))) j

theorem upperPolynomial_actual (k : ℕ) (c : Fin 4) :
    upperPolynomial k c = ((blockB k).submatrix id c.succAbove).permanent := by
  simp [upperPolynomial, Matrix.permanent, ComponentUpperSeed.genericB, blockB,
    Matrix.submatrix, map_sum, map_prod]

theorem lowerPolynomial_actual (k : ℕ) : lowerPolynomial k = (blockW k).permanent := by
  simp [lowerPolynomial, Matrix.permanent, genericW, blockW, map_sum, map_prod]

theorem proportionality_actual (k : ℕ) (ij : Fin 2 × Fin k) :
    proportionality k ij = blockV k 0 0 * blockV k ij.1.succ ij.2.succ -
      blockV k ij.1.succ 0 * blockV k 0 ij.2.succ := by
  simp [proportionality, blockV]

theorem ambient_variable_count (k : ℕ) : Fintype.card (Variables k) = (3+(k+1))^2 := by
  simp [Variables, BIndex, WIndex, LIndex, VIndex]
  ring

#print axioms jacobian_det
#print axioms full_jacobian_rank
#print axioms upperPolynomial_actual
#print axioms proportionality_actual
#print axioms jacobian_block

end
end ComponentChartJacobian
