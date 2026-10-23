import CriticalContainment

/-!
# Translation of the actual polynomial family to an arbitrary complex parameter

All constructions use the accepted polynomial ring P and its actual matrix N.
Translation sends x0 to x0 + C(s-2), fixes the other fifteen variables and all
coefficients, and therefore sends t = 2+x0 to s+x0. The translated permanent
polynomials lie in the unchanged actual target ideal, without a degree cutoff,
coefficient-table hypothesis, or rank assumption. No localized equality is
claimed here.
-/

namespace ParametricLocalGeometry
open MvPolynomial ConcreteLocalGeometry

/-- Translation along the free family parameter; the remaining variables are fixed. -/
noncomputable def translation (s : ℂ) : P →+* P :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i => if i = 0 then x 0 + MvPolynomial.C (s - 2) else x i)

@[simp] theorem translation_C (s c : ℂ) :
    translation s (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [translation]

@[simp] theorem translation_x_zero (s : ℂ) :
    translation s (x 0) = x 0 + MvPolynomial.C (s - 2) := by
  simp [translation, x]

@[simp] theorem translation_x_of_ne_zero (s : ℂ) (i : Fin 16) (hi : i ≠ 0) :
    translation s (x i) = x i := by
  simp [translation, x, hi]

/-- The original t is transformed into the exact parameter s plus x0. -/
theorem translation_t (s : ℂ) : translation s t = MvPolynomial.C s + x 0 := by
  simp [t, map_sub]
  ring

/-- The actual matrix, translated entry by entry. -/
noncomputable def translatedN (s : ℂ) : Matrix (Fin 5) (Fin 5) P :=
  N.map (translation s)

/-- The permanent equations of the translated actual matrix. -/
noncomputable def translatedEquation (s : ℂ) (ij : Fin 5 × Fin 5) : P :=
  ((translatedN s).submatrix ij.1.succAbove ij.2.succAbove).permanent

noncomputable def translatedCriticalIdeal (s : ℂ) : Ideal P :=
  Ideal.span (Set.range (translatedEquation s))

/-- Permanent commutes with this genuine ring homomorphism. -/
theorem translation_permanent (s : ℂ) {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n P) :
    translation s M.permanent = (M.map (translation s)).permanent := by
  simp [Matrix.permanent]

/-- These are the translated original equations, not an unrelated family. -/
theorem translatedEquation_eq_translation (s : ℂ) (ij : Fin 5 × Fin 5) :
    translatedEquation s ij = translation s (equation ij) := by
  rw [equation, translation_permanent]
  rfl

/-- Every one of the actual fifteen target generators is fixed. -/
@[simp] theorem translation_targetGenerator (s : ℂ) (j : Fin 15) :
    translation s (targetGenerator j) = targetGenerator j := by
  fin_cases j <;> simp [targetGenerator]

/-- Translation preserves the actual target ideal by its explicit generators. -/
theorem translation_preserves_target (s : ℂ) :
    targetIdeal ≤ Ideal.comap (translation s) targetIdeal := by
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  change translation s (targetGenerator j) ∈ targetIdeal
  rw [translation_targetGenerator]
  exact Ideal.subset_span (Set.mem_range_self j)

/-- In fact the image ideal is exactly the unchanged target ideal. -/
theorem translation_map_target (s : ℂ) :
    Ideal.map (translation s) targetIdeal = targetIdeal := by
  apply le_antisymm (Ideal.map_le_iff_le_comap.mpr (translation_preserves_target s))
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  rw [← translation_targetGenerator s j]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self j))

/-- All 25 full polynomial permanent equations belong to the unchanged J,
    uniformly for every complex parameter s. -/
theorem translatedEquation_mem_target (s : ℂ) (r c : Fin 5) :
    translatedEquation s (r, c) ∈ targetIdeal := by
  rw [translatedEquation_eq_translation]
  exact translation_preserves_target s (equation_mem_target r c)

/-- Consequently the entire translated critical ideal is contained in J. -/
theorem translatedCriticalIdeal_le_targetIdeal (s : ℂ) :
    translatedCriticalIdeal s ≤ targetIdeal := by
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨r, c⟩, rfl⟩
  exact translatedEquation_mem_target s r c


end ParametricLocalGeometry

#print axioms ParametricLocalGeometry.translation_t
#print axioms ParametricLocalGeometry.translation_permanent
#print axioms ParametricLocalGeometry.translatedEquation_eq_translation
#print axioms ParametricLocalGeometry.translation_targetGenerator
#print axioms ParametricLocalGeometry.translation_map_target
#print axioms ParametricLocalGeometry.translatedEquation_mem_target
#print axioms ParametricLocalGeometry.translatedCriticalIdeal_le_targetIdeal

