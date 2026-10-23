import FamilyContainment.IdealContainment
import UpperSeed.LiteralUpper

set_option backward.isDefEq.respectTransparency false
namespace ComponentFamilyContainment
open Matrix Equiv
variable {R : Type*} [CommRing R]

/-- Family containment stated using exactly the four standard maximal
permanents of the literal 3-by-4 matrix B. -/
theorem literal_family_cofactors_zero {k : ℕ} (B : Matrix (Fin 3) (Fin 4) R)
    (lam : Fin (k+1) → R) (W : Matrix (Fin (k+1)) (Fin (k+1)) R)
    (hW : W.permanent = 0)
    (hB : ∀ c : Fin 4, (B.submatrix id c.succAbove).permanent = 0)
    (r c : Fin (3+k+1)) :
    ((familyFin (B.submatrix id Fin.castSucc) (fun i => B i 3) lam W).submatrix
      r.succAbove c.succAbove).permanent = 0 := by
  obtain ⟨hU, hA⟩ := ComponentLiteralUpper.upper_conditions_of_maximal_permanents B hB
  exact all_fin_cofactors_zero _ _ _ _ hW hU hA r c

/-- The five family equations: four upper maximal permanents and per W. -/
def familyEquationIdeal {k : ℕ} (B : Matrix (Fin 3) (Fin 4) R)
    (W : Matrix (Fin (k+1)) (Fin (k+1)) R) : Ideal R :=
  Ideal.span (insert W.permanent (Set.range (fun c : Fin 4 => (B.submatrix id c.succAbove).permanent)))

/-- Exact ideal containment for every substituted submaximal permanent. -/
theorem literal_family_cofactors_mem {k : ℕ} (B : Matrix (Fin 3) (Fin 4) R)
    (lam : Fin (k+1) → R) (W : Matrix (Fin (k+1)) (Fin (k+1)) R)
    (r c : Fin (3+k+1)) :
    ((familyFin (B.submatrix id Fin.castSucc) (fun i => B i 3) lam W).submatrix
      r.succAbove c.succAbove).permanent ∈ familyEquationIdeal B W := by
  apply all_fin_cofactors_mem_ideal
  · exact Ideal.subset_span (Set.mem_insert _ _)
  · rw [ComponentLiteralUpper.first_three_is_literal_minor]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨3, rfl⟩)
  · intro j
    rw [ComponentLiteralUpper.augmented_is_literal_minor]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨j.castSucc, rfl⟩)

/-- Ideal of all substituted submaximal equations is contained in the five-equation
family ideal. This is a uniform ring-theoretic identity, not a sample check. -/
theorem literal_pullback_ideal_le {k : ℕ} (B : Matrix (Fin 3) (Fin 4) R)
    (lam : Fin (k+1) → R) (W : Matrix (Fin (k+1)) (Fin (k+1)) R) :
    Ideal.span (Set.range (fun rc : Fin (3+k+1) × Fin (3+k+1) =>
      ((familyFin (B.submatrix id Fin.castSucc) (fun i => B i 3) lam W).submatrix
        rc.1.succAbove rc.2.succAbove).permanent)) ≤ familyEquationIdeal B W := by
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨r,c⟩, rfl⟩
  exact literal_family_cofactors_mem B lam W r c

#print axioms literal_family_cofactors_zero
#print axioms literal_pullback_ideal_le
end ComponentFamilyContainment
