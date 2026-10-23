import FullHessianRank.GradientCofactors
import ActualLocalChart.IdealEquality
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ComponentCanonicalProblem
noncomputable section
open Matrix MvPolynomial ComponentChartJacobian ComponentAmbientHessian
open ComponentFullHessianRank ComponentActualLocalChart

abbrev Coordinates (k : ℕ) := Fin (3+k+1) × Fin (3+k+1)
abbrev PolynomialRing (k : ℕ) := MvPolynomial (Coordinates k) ℂ

def genericMatrix (k : ℕ) : Matrix (Fin (3+k+1)) (Fin (3+k+1)) (PolynomialRing k) :=
  fun i j => X (i,j)

def permanentPolynomial (k : ℕ) : PolynomialRing k := (genericMatrix k).permanent

def cofactor (k : ℕ) (ij : Coordinates k) : PolynomialRing k :=
  ((genericMatrix k).submatrix ij.1.succAbove ij.2.succAbove).permanent

def cofactorIdeal (k : ℕ) : Ideal (PolynomialRing k) := Ideal.span (Set.range (cofactor k))
abbrev CoordinateAlgebra (k : ℕ) := PolynomialRing k ⧸ cofactorIdeal k

def coordinateEquiv (k : ℕ) : P k ≃ₐ[ℂ] PolynomialRing k :=
  MvPolynomial.renameEquiv ℂ (finiteEntryEquiv k)

theorem finiteAmbient_map (k : ℕ) :
    (finiteAmbient k).map (coordinateEquiv k) = genericMatrix k := by
  ext i j
  simp [finiteAmbient_entry, coordinateEquiv, MvPolynomial.renameEquiv, genericMatrix]

theorem permanent_compatibility (k : ℕ) :
    coordinateEquiv k (actualPolynomial k) = permanentPolynomial k := by
  rw [← finiteAmbient_permanent]
  change (coordinateEquiv k).toRingHom (finiteAmbient k).permanent = _
  rw [← ComponentFamilyContainment.permanent_map (coordinateEquiv k).toRingHom]
  rw [show (finiteAmbient k).map (coordinateEquiv k).toRingHom = genericMatrix k from finiteAmbient_map k]
  rfl

theorem determinant_compatibility (k : ℕ) :
    coordinateEquiv k (finiteAmbient k).det = (genericMatrix k).det := by
  change (coordinateEquiv k).toRingHom (finiteAmbient k).det = _
  rw [RingHom.map_det (coordinateEquiv k).toRingHom]
  change ((finiteAmbient k).map (coordinateEquiv k).toRingHom).det = _
  rw [show (finiteAmbient k).map (coordinateEquiv k).toRingHom = genericMatrix k from finiteAmbient_map k]

theorem gradient_compatibility (k : ℕ) (x : Variables k) :
    coordinateEquiv k (pderiv x (actualPolynomial k)) = cofactor k (finiteEntryEquiv k x) := by
  rw [actual_gradient_eq_cofactor]
  change (coordinateEquiv k).toRingHom ((finiteAmbient k).submatrix (finiteEntryEquiv k x).1.succAbove (finiteEntryEquiv k x).2.succAbove).permanent = _
  rw [← ComponentFamilyContainment.permanent_map (coordinateEquiv k).toRingHom]
  have hm : ((finiteAmbient k).submatrix (finiteEntryEquiv k x).1.succAbove
      (finiteEntryEquiv k x).2.succAbove).map (coordinateEquiv k).toRingHom =
      (genericMatrix k).submatrix (finiteEntryEquiv k x).1.succAbove
        (finiteEntryEquiv k x).2.succAbove := by
    change ((finiteAmbient k).map (coordinateEquiv k)).submatrix (finiteEntryEquiv k x).1.succAbove (finiteEntryEquiv k x).2.succAbove = _
    rw [finiteAmbient_map]
  rw [hm]
  rfl

theorem ideal_compatibility (k : ℕ) :
    (actualGradientIdeal k).map (coordinateEquiv k).toRingHom = cofactorIdeal k := by
  unfold actualGradientIdeal cofactorIdeal
  rw [Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨q, ⟨x, rfl⟩, rfl⟩
    exact ⟨finiteEntryEquiv k x, (gradient_compatibility k x).symm⟩
  · rintro ⟨ij, rfl⟩
    refine ⟨pderiv ((finiteEntryEquiv k).symm ij) (actualPolynomial k), ?_, ?_⟩
    · exact ⟨_, rfl⟩
    · simpa using gradient_compatibility k ((finiteEntryEquiv k).symm ij)

/-- Statement fidelity: the grouped actual gradient quotient is algebraically
identical to the standard independent-entry submaximal permanental quotient. -/
def coordinateAlgebraEquiv (k : ℕ) :
    (P k ⧸ actualGradientIdeal k) ≃ₐ[ℂ] CoordinateAlgebra k :=
  Ideal.quotientEquivAlg (actualGradientIdeal k) (cofactorIdeal k)
    (coordinateEquiv k) (ideal_compatibility k).symm

def canonicalSeed (k : ℕ) : Coordinates k → ℂ := fun ij => seed k ((finiteEntryEquiv k).symm ij)

theorem seed_evaluation_compatibility (k : ℕ) (p : P k) :
    eval (canonicalSeed k) (coordinateEquiv k p) = eval (seed k) p := by
  change eval (canonicalSeed k) (rename (finiteEntryEquiv k) p) = _
  rw [eval_rename]
  have he : canonicalSeed k ∘ finiteEntryEquiv k = seed k := by
    funext x
    simp [canonicalSeed]
  rw [he]

#print axioms coordinateAlgebraEquiv
#print axioms permanent_compatibility
#print axioms determinant_compatibility
#print axioms seed_evaluation_compatibility
end
end ComponentCanonicalProblem
