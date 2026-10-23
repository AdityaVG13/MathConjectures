import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.AtPrime.Basic

namespace UniformComponentGeometry

variable {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ]

/-- Polynomial or localized coefficient identities imply honest ideal containment. -/
theorem span_mulVec_le (A : Matrix ι κ R) (g : κ → R) :
    Ideal.span (Set.range (A.mulVec g)) ≤ Ideal.span (Set.range g) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact Submodule.sum_mem _ (fun j _ => Ideal.mul_mem_left _ _
    (Ideal.subset_span ⟨j, rfl⟩))

/-- A left inverse for a coefficient matrix proves equality of the actual generated ideals.
This avoids an abstract conormal bridge once exact coefficient identities are known. -/
theorem span_mulVec_eq_of_left_inverse [DecidableEq κ]
    (A : Matrix ι κ R) (B : Matrix κ ι R) (h : B * A = 1) (g : κ → R) :
    Ideal.span (Set.range (A.mulVec g)) = Ideal.span (Set.range g) := by
  apply le_antisymm (span_mulVec_le A g)
  have hi : B.mulVec (A.mulVec g) = g := by
    rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  simpa only [hi] using span_mulVec_le B (A.mulVec g)

/-- A unit determinant for a square coefficient matrix suffices over any commutative ring. -/
theorem span_mulVec_eq_of_isUnit_det [DecidableEq ι]
    (A : Matrix ι ι R) (h : IsUnit A.det) (g : ι → R) :
    Ideal.span (Set.range (A.mulVec g)) = Ideal.span (Set.range g) :=
  span_mulVec_eq_of_left_inverse A A⁻¹ (Matrix.nonsing_inv_mul A h) g

section Localization

variable {S K : Type*} [CommRing S] [Algebra R S] [Field K]

/-- Nonvanishing of a determinant at a prime makes the localized coefficient matrix invertible. -/
theorem isUnit_localized_det_of_not_mem [DecidableEq ι]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p]
    (A : Matrix ι ι R) (h : A.det ∉ p) :
    IsUnit (A.map (algebraMap R S)).det := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (IsLocalization.AtPrime.isUnit_to_map_iff S p A.det).mpr h

attribute [local instance] RingHom.ker_isPrime

/-- Specialization to the prime cut out by a field-valued evaluation map. -/
theorem isUnit_localized_det_of_eval_ne_zero [DecidableEq ι]
    (ev : R →+* K) [IsLocalization.AtPrime S (RingHom.ker ev)]
    (A : Matrix ι ι R) (h : (A.map ev).det ≠ 0) :
    IsUnit (A.map (algebraMap R S)).det := by
  apply isUnit_localized_det_of_not_mem (RingHom.ker ev) A
  simpa only [RingHom.mem_ker, RingHom.map_det, RingHom.mapMatrix_apply] using h

/-- Exact coefficient identities and a nonzero evaluated determinant prove equality of
localized generator ideals. This is applicable to a selected square list of actual cofactors. -/
theorem localized_span_eq_of_eval_det_ne_zero [DecidableEq ι]
    (ev : R →+* K) [IsLocalization.AtPrime S (RingHom.ker ev)]
    (A : Matrix ι ι R) (g f : ι → R) (hfg : f = A.mulVec g)
    (h : (A.map ev).det ≠ 0) :
    Ideal.span (Set.range (fun i => algebraMap R S (f i))) =
      Ideal.span (Set.range (fun i => algebraMap R S (g i))) := by
  have hv : (fun i => algebraMap R S (f i)) =
      (A.map (algebraMap R S)).mulVec (fun i => algebraMap R S (g i)) := by
    funext i
    rw [hfg, RingHom.map_mulVec]
    rfl
  rw [hv]
  exact span_mulVec_eq_of_isUnit_det _
    (isUnit_localized_det_of_eval_ne_zero ev A h) _

/-- A selected square subsystem suffices for the entire actual ideal: no assertion that the
chosen equations generate globally is required. The opposite containment is explicit. -/
theorem localized_ideal_eq_of_selected_eval_det_ne_zero [DecidableEq ι]
    (ev : R →+* K) [IsLocalization.AtPrime S (RingHom.ker ev)]
    (I : Ideal R) (A : Matrix ι ι R) (g f : ι → R)
    (hcontain : I ≤ Ideal.span (Set.range g)) (hselected : ∀ i, f i ∈ I)
    (hfg : f = A.mulVec g) (h : (A.map ev).det ≠ 0) :
    I.map (algebraMap R S) = (Ideal.span (Set.range g)).map (algebraMap R S) := by
  apply le_antisymm (Ideal.map_mono hcontain)
  have hs : Ideal.span (Set.range f) ≤ I := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hselected i
  have he : (Ideal.span (Set.range f)).map (algebraMap R S) =
      (Ideal.span (Set.range g)).map (algebraMap R S) := by
    simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def] using
      localized_span_eq_of_eval_det_ne_zero (S := S) ev A g f hfg h
  rw [← he]
  exact Ideal.map_mono hs

end Localization

#print axioms span_mulVec_eq_of_isUnit_det
#print axioms localized_span_eq_of_eval_det_ne_zero
#print axioms localized_ideal_eq_of_selected_eval_det_ne_zero
end UniformComponentGeometry
