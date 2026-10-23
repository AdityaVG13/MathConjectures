import CanonicalProblem.FullComponent
import CanonicalProblem.SizeReindex

set_option autoImplicit false
namespace ComponentCanonicalProblem
open PrimeSpectrum

/-- All matrix sizes n≥5. The witness k includes an explicit equality between
the canonical independent-entry matrix size and n; no silent type reindexing
or coordinate identification is hidden in the statement. -/
theorem full_component_exists_every_size (n : ℕ) (hn : 5 ≤ n) :
    ∃ k : ℕ, 3+k+1 = n ∧
      ∃ P : Ideal (CoordinateAlgebra k), IsMinimalPrime P ∧
        ringKrullDim (CoordinateAlgebra k ⧸ P) = ((n^2-5*n+12 : ℕ) : WithBot ℕ∞) ∧
        zeroLocus (P : Set (CoordinateAlgebra k)) ∈
          irreducibleComponents (PrimeSpectrum (CoordinateAlgebra k)) ∧
        ∃ f : CoordinateAlgebra k, ∃ U : Set (PrimeSpectrum (CoordinateAlgebra k)),
          U = zeroLocus P ∩ (basicOpen f : Set (PrimeSpectrum (CoordinateAlgebra k))) ∧
          U.Nonempty ∧ closure U = zeroLocus P ∧
          (∀ x ∈ U, x ∈ Algebra.smoothLocus ℂ (CoordinateAlgebra k) ∧
            canonicalDeterminant k ∉ x.asIdeal) := by
  refine ⟨n-4, canonical_size n hn, ?_⟩
  have hh := full_component_exists (n-4) (parameter_positive n hn)
  simpa only [canonical_dimension n hn] using hh

#print axioms full_component_exists_every_size
#print full_component_exists_every_size
end ComponentCanonicalProblem
