import ChartJacobian.ChartJacobian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ComponentChartJacobian
noncomputable section
open MvPolynomial Matrix Equiv

abbrev Axis (k : ℕ) := Fin 3 ⊕ Fin (k+1)

/-- Explicit bijection from the grouped polynomial variables to all ambient
matrix entries. In particular no ambient variable is omitted or identified. -/
def entryEquiv (k : ℕ) : Variables k ≃ (Axis k × Axis k) where
  toFun x := match x with
    | Sum.inl (i,j) => Fin.lastCases (Sum.inl i, Sum.inr 0)
        (fun c => (Sum.inl i, Sum.inl c)) j
    | Sum.inr (Sum.inl (i,j)) => (Sum.inr i, Sum.inr j)
    | Sum.inr (Sum.inr (Sum.inl (i,j))) => (Sum.inr i, Sum.inl j)
    | Sum.inr (Sum.inr (Sum.inr (i,j))) => (Sum.inl i, Sum.inr j.succ)
  invFun x := match x with
    | (Sum.inl i, Sum.inl j) => bVar (i,j.castSucc)
    | (Sum.inl i, Sum.inr j) => Fin.cases (bVar (i,3)) (fun c => vVar (i,c)) j
    | (Sum.inr i, Sum.inl j) => lVar (i,j)
    | (Sum.inr i, Sum.inr j) => wVar (i,j)
  left_inv x := by
    rcases x with ⟨i,j⟩ | (⟨i,j⟩ | (⟨i,j⟩ | ⟨i,j⟩))
    · refine Fin.lastCases ?_ (fun c => ?_) j
      · simp only [Fin.lastCases_last, Fin.cases_zero]
        rfl
      · simp [bVar]
    · rfl
    · rfl
    · simp [vVar]
  right_inv x := by
    rcases x with ⟨i | i,j | j⟩
    · simp [bVar, show (3 : Fin 4) = Fin.last 3 from rfl]
    · refine Fin.cases ?_ (fun c => ?_) j
      · simp only [Fin.cases_zero]
        exact Fin.lastCases_last
      · simp [vVar]
    · rfl
    · rfl

def actualAmbient (k : ℕ) : Matrix (Axis k) (Axis k) (P k) :=
  fun i j => X ((entryEquiv k).symm (i,j))

theorem actualAmbient_blocks (k : ℕ) : actualAmbient k =
    Matrix.fromBlocks ((blockB k).submatrix id Fin.castSucc)
      (blockV k) (blockL k) (blockW k) := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · change X (R := ℂ) (Fin.cases (bVar (k := k) (i,3)) (fun c => vVar (i,c)) j) =
      Fin.cases (X (bVar (i,3))) (fun c => X (vVar (i,c))) j
    refine Fin.cases ?_ (fun c => ?_) j <;> rfl
  · rfl
  · rfl

#print axioms actualAmbient_blocks
end
end ComponentChartJacobian
