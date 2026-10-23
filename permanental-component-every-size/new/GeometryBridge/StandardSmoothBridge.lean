import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.Locus

namespace UniformComponentGeometry

variable {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Finite ι] [Finite σ]

/-- A finite presentation with a unit selected Jacobian defines an actually smooth algebra. -/
theorem smooth_of_unit_presentation_jacobian
    (P : Algebra.PreSubmersivePresentation R S ι σ) (h : IsUnit P.jacobian) :
    Algebra.Smooth R S := by
  let Q : Algebra.SubmersivePresentation R S ι σ := { P with jacobian_isUnit := h }
  letI := Q.isStandardSmooth
  infer_instance

/-- If such a presentation describes an actual principal localization, the whole principal open
lies in the smooth locus of the original algebra. Equality with the actual localization must
be established before applying this theorem; no replacement of its defining ideal is assumed. -/
theorem basicOpen_subset_smoothLocus_of_unit_presentation_jacobian
    [Algebra.FinitePresentation R S] (f : S)
    (P : Algebra.PreSubmersivePresentation R (Localization.Away f) ι σ)
    (h : IsUnit P.jacobian) :
    (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum S)) ⊆ Algebra.smoothLocus R S := by
  exact Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr
    (smooth_of_unit_presentation_jacobian P h)

#print axioms basicOpen_subset_smoothLocus_of_unit_presentation_jacobian
end UniformComponentGeometry
