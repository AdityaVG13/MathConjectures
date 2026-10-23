import FullChart.Elimination
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option backward.isDefEq.respectTransparency false
namespace DisjointPolynomialQuotient
noncomputable section
open MvPolynomial
open scoped TensorProduct
variable {R σ τ ι κ : Type*} [CommRing R]
variable (f : ι → MvPolynomial σ R) (g : κ → MvPolynomial τ R)
def leftIdeal : Ideal (MvPolynomial σ R) := Ideal.span (Set.range f)
def rightIdeal : Ideal (MvPolynomial τ R) := Ideal.span (Set.range g)
def equations : ι ⊕ κ → MvPolynomial (σ ⊕ τ) R
  | .inl i => rename Sum.inl (f i)
  | .inr j => rename Sum.inr (g j)
def jointIdeal : Ideal (MvPolynomial (σ ⊕ τ) R) := Ideal.span (Set.range (equations f g))
abbrev L := MvPolynomial σ R ⧸ leftIdeal f
abbrev U := MvPolynomial τ R ⧸ rightIdeal g
abbrev Q := MvPolynomial (σ ⊕ τ) R ⧸ jointIdeal f g
abbrev T := L f ⊗[R] U g

def leftPoly : MvPolynomial σ R →ₐ[R] Q f g :=
  (Ideal.Quotient.mkₐ R _).comp (rename Sum.inl)
def rightPoly : MvPolynomial τ R →ₐ[R] Q f g :=
  (Ideal.Quotient.mkₐ R _).comp (rename Sum.inr)

theorem leftPoly_zero (i : ι) : leftPoly f g (f i) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span ⟨Sum.inl i,rfl⟩
theorem rightPoly_zero (i : κ) : rightPoly f g (g i) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span ⟨Sum.inr i,rfl⟩

def left : L f →ₐ[R] Q f g := Ideal.Quotient.liftₐ _ (leftPoly f g) (by
  change leftIdeal f ≤ RingHom.ker (leftPoly f g)
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact leftPoly_zero f g i)
def right : U g →ₐ[R] Q f g := Ideal.Quotient.liftₐ _ (rightPoly f g) (by
  change rightIdeal g ≤ RingHom.ker (rightPoly f g)
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact rightPoly_zero f g i)
def backward : T f g →ₐ[R] Q f g :=
  Algebra.TensorProduct.lift (left f g) (right f g) (fun _ _ => Commute.all _ _)

def forwardPoly : MvPolynomial (σ ⊕ τ) R →ₐ[R] T f g := aeval (Sum.elim
  (fun i => (Algebra.TensorProduct.includeLeft : L f →ₐ[R] T f g) (Ideal.Quotient.mk (leftIdeal f) (X i)))
  (fun j => (Algebra.TensorProduct.includeRight : U g →ₐ[R] T f g) (Ideal.Quotient.mk (rightIdeal g) (X j))))

theorem forwardPoly_left : (forwardPoly f g).comp (rename Sum.inl) =
    Algebra.TensorProduct.includeLeft.comp (Ideal.Quotient.mkₐ R (leftIdeal f)) := by
  ext i
  simp [forwardPoly]
theorem forwardPoly_right : (forwardPoly f g).comp (rename Sum.inr) =
    Algebra.TensorProduct.includeRight.comp (Ideal.Quotient.mkₐ R (rightIdeal g)) := by
  ext i
  simp [forwardPoly]

theorem forwardPoly_zero (i : ι ⊕ κ) : forwardPoly f g (equations f g i) = 0 := by
  cases i with
  | inl i =>
    change (forwardPoly f g).comp (rename Sum.inl) (f i) = 0
    rw [forwardPoly_left]
    simp only [AlgHom.comp_apply,Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (show f i ∈ leftIdeal f from Ideal.subset_span (Set.mem_range_self i)),map_zero]
  | inr i =>
    change (forwardPoly f g).comp (rename Sum.inr) (g i) = 0
    rw [forwardPoly_right]
    simp only [AlgHom.comp_apply,Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (show g i ∈ rightIdeal g from Ideal.subset_span (Set.mem_range_self i)),map_zero]

def forward : Q f g →ₐ[R] T f g := Ideal.Quotient.liftₐ _ (forwardPoly f g) (by
  change jointIdeal f g ≤ RingHom.ker (forwardPoly f g)
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact forwardPoly_zero f g i)

theorem backward_forward : (backward f g).comp (forward f g) = AlgHom.id R (Q f g) := by
  apply Ideal.Quotient.algHom_ext
  ext i
  cases i <;> simp [backward,forward,forwardPoly,left,right,leftPoly,rightPoly,
    Algebra.TensorProduct.includeLeft,Algebra.TensorProduct.includeRight]

theorem forward_backward : (forward f g).comp (backward f g) = AlgHom.id R (T f g) := by
  apply Algebra.TensorProduct.ext
  · apply Ideal.Quotient.algHom_ext
    ext i
    simp [backward,forward,forwardPoly,left,right,leftPoly,rightPoly,
      Algebra.TensorProduct.includeLeft,Algebra.TensorProduct.includeRight]
  · apply Ideal.Quotient.algHom_ext
    ext i
    simp [backward,forward,forwardPoly,left,right,leftPoly,rightPoly,
      Algebra.TensorProduct.includeLeft,Algebra.TensorProduct.includeRight]

/-- Quotienting independent groups of variables by their own equations commutes with tensor product. -/
def equivalence : Q f g ≃ₐ[R] T f g :=
  AlgEquiv.ofAlgHom (forward f g) (backward f g) (forward_backward f g) (backward_forward f g)
end
end DisjointPolynomialQuotient
#print axioms DisjointPolynomialQuotient.equivalence

namespace DisjointPolynomialQuotient
noncomputable section
open MvPolynomial
open scoped TensorProduct
variable {R σ τ ι κ : Type*} [CommRing R]
variable (f : ι → MvPolynomial σ R) (g : κ → MvPolynomial τ R)

@[simp] theorem equivalence_mk_left (p : MvPolynomial σ R) :
    equivalence f g (Ideal.Quotient.mk (jointIdeal f g) (rename Sum.inl p)) =
      (Algebra.TensorProduct.includeLeft : L f →ₐ[R] T f g) (Ideal.Quotient.mk (leftIdeal f) p) := by
  change forwardPoly f g (rename Sum.inl p) = _
  exact AlgHom.congr_fun (forwardPoly_left f g) p
@[simp] theorem equivalence_mk_right (p : MvPolynomial τ R) :
    equivalence f g (Ideal.Quotient.mk (jointIdeal f g) (rename Sum.inr p)) =
      (Algebra.TensorProduct.includeRight : U g →ₐ[R] T f g) (Ideal.Quotient.mk (rightIdeal g) p) := by
  change forwardPoly f g (rename Sum.inr p) = _
  exact AlgHom.congr_fun (forwardPoly_right f g) p
@[simp] theorem equivalence_mk_X_left (i : σ) :
    equivalence f g (Ideal.Quotient.mk (jointIdeal f g) (X (Sum.inl i))) =
      (Algebra.TensorProduct.includeLeft : L f →ₐ[R] T f g) (Ideal.Quotient.mk (leftIdeal f) (X i)) := by
  simpa using equivalence_mk_left f g (X i)
@[simp] theorem equivalence_mk_X_right (i : τ) :
    equivalence f g (Ideal.Quotient.mk (jointIdeal f g) (X (Sum.inr i))) =
      (Algebra.TensorProduct.includeRight : U g →ₐ[R] T f g) (Ideal.Quotient.mk (rightIdeal g) (X i)) := by
  simpa using equivalence_mk_right f g (X i)
end
end DisjointPolynomialQuotient

namespace UniformFullChart
noncomputable section
open MvPolynomial ComponentChartJacobian
open scoped TensorProduct

def upperRawEquation (c : Fin 4) : MvPolynomial BIndex ℂ :=
  (ComponentUpperSeed.genericB.submatrix id c.succAbove).permanent
def lowerRawEquation (k : ℕ) (_ : Unit) : MvPolynomial (WIndex k) ℂ := (genericW k).permanent
def upperRawIdeal : Ideal (MvPolynomial BIndex ℂ) := Ideal.span (Set.range upperRawEquation)
def lowerRawIdeal (k : ℕ) : Ideal (MvPolynomial (WIndex k) ℂ) :=
  Ideal.span (Set.range (lowerRawEquation k))
abbrev UpperRawQuot := MvPolynomial BIndex ℂ ⧸ upperRawIdeal
abbrev LowerRawQuot (k : ℕ) := MvPolynomial (WIndex k) ℂ ⧸ lowerRawIdeal k
abbrev RetainedTensor (k : ℕ) := UpperRawQuot ⊗[ℂ] LowerRawQuot k

theorem lowerRawIdeal_singleton (k : ℕ) :
    lowerRawIdeal k = Ideal.span {(genericW k).permanent} := by
  change Ideal.span (Set.range (fun _ : Unit => (genericW k).permanent)) = _
  rw [Set.range_const]

theorem baseIdeal_eq_disjoint (k : ℕ) : baseIdeal k =
    DisjointPolynomialQuotient.jointIdeal upperRawEquation (lowerRawEquation k) := by
  unfold baseIdeal DisjointPolynomialQuotient.jointIdeal
  congr 1
  congr 1
  funext r
  cases r <;> rfl

/-- The actual retained B/W equation quotient splits, without any assumed decomposition,
into the tensor product of the actual upper and lower permanent quotients. -/
def retainedTensorEquiv (k : ℕ) : BaseQuot k ≃ₐ[ℂ] RetainedTensor k :=
  (Ideal.quotientEquivAlgOfEq ℂ (baseIdeal_eq_disjoint k)).trans
    (DisjointPolynomialQuotient.equivalence upperRawEquation (lowerRawEquation k))

@[simp] theorem retainedTensorEquiv_upper (k : ℕ) (p : MvPolynomial BIndex ℂ) :
    retainedTensorEquiv k (Ideal.Quotient.mk (baseIdeal k) (rename Sum.inl p)) =
      (Algebra.TensorProduct.includeLeft : UpperRawQuot →ₐ[ℂ] RetainedTensor k)
        (Ideal.Quotient.mk upperRawIdeal p) :=
  by
    simp only [retainedTensorEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
    exact
      DisjointPolynomialQuotient.equivalence_mk_left upperRawEquation (lowerRawEquation k) p
@[simp] theorem retainedTensorEquiv_lower (k : ℕ) (p : MvPolynomial (WIndex k) ℂ) :
    retainedTensorEquiv k (Ideal.Quotient.mk (baseIdeal k) (rename Sum.inr p)) =
      (Algebra.TensorProduct.includeRight : LowerRawQuot k →ₐ[ℂ] RetainedTensor k)
        (Ideal.Quotient.mk (lowerRawIdeal k) p) :=
  by
    simp only [retainedTensorEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
    exact
      DisjointPolynomialQuotient.equivalence_mk_right upperRawEquation (lowerRawEquation k) p
@[simp] theorem retainedTensorEquiv_X_upper (k : ℕ) (i : BIndex) :
    retainedTensorEquiv k (Ideal.Quotient.mk (baseIdeal k) (X (.inl i))) =
      (Algebra.TensorProduct.includeLeft : UpperRawQuot →ₐ[ℂ] RetainedTensor k)
        (Ideal.Quotient.mk upperRawIdeal (X i)) := by
  simpa using retainedTensorEquiv_upper k (X i)
@[simp] theorem retainedTensorEquiv_X_lower (k : ℕ) (i : WIndex k) :
    retainedTensorEquiv k (Ideal.Quotient.mk (baseIdeal k) (X (.inr i))) =
      (Algebra.TensorProduct.includeRight : LowerRawQuot k →ₐ[ℂ] RetainedTensor k)
        (Ideal.Quotient.mk (lowerRawIdeal k) (X i)) := by
  simpa using retainedTensorEquiv_lower k (X i)
@[simp] theorem retainedTensorEquiv_pivot (k : ℕ) :
    retainedTensorEquiv k (basePivot k) =
      (Algebra.TensorProduct.includeLeft : UpperRawQuot →ₐ[ℂ] RetainedTensor k)
        (Ideal.Quotient.mk upperRawIdeal (X (0,3))) := retainedTensorEquiv_X_upper k (0,3)
end
end UniformFullChart
#print axioms UniformFullChart.retainedTensorEquiv
