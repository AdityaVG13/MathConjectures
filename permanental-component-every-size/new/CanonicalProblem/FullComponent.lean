import CanonicalProblem.SeedComponent
import ActualLocalChart.PrincipalGeometry
import FullChart.CertifiedSeed

set_option autoImplicit false
namespace ComponentCanonicalProblem
noncomputable section
open PrimeSpectrum ComponentActualLocalChart

/-- For every matrix size k+4 ≥ 5, the scheme defined by all unsigned
submaximal permanents has an irreducible component of dimension k²+3k+8,
with a nonempty dense relatively principal open where the ambient scheme
is smooth and the actual generic matrix determinant is nonzero.
No chart, rank, dimension, smoothness, or nonemptiness hypotheses remain. -/
theorem full_component_exists (k : ℕ) (hk : 1 ≤ k) :
    ∃ P : Ideal (CoordinateAlgebra k), IsMinimalPrime P ∧
      ringKrullDim (CoordinateAlgebra k ⧸ P) = ((k^2+3*k+8 : ℕ) : WithBot ℕ∞) ∧
      zeroLocus (P : Set (CoordinateAlgebra k)) ∈
        irreducibleComponents (PrimeSpectrum (CoordinateAlgebra k)) ∧
      ∃ f : CoordinateAlgebra k, ∃ U : Set (PrimeSpectrum (CoordinateAlgebra k)),
        U = zeroLocus P ∩ (basicOpen f : Set (PrimeSpectrum (CoordinateAlgebra k))) ∧
        U.Nonempty ∧ closure U = zeroLocus P ∧
        (∀ x ∈ U, x ∈ Algebra.smoothLocus ℂ (CoordinateAlgebra k) ∧
          canonicalDeterminant k ∉ x.asIdeal) := by
  obtain ⟨f,hf,hs,hd⟩ := exists_actual_smooth_principal_chart k
    (UniformFullChart.rawChartDenominator_ne_zero_at_seed k)
  letI := hs
  obtain ⟨P,hP,hpd,hpc,U,hU,hne,hcl,hsm⟩ :=
    canonical_component_from_grouped_chart_and_seed k hk f hf hd
  exact ⟨P,hP,hpd,hpc,coordinateAlgebraEquiv k f * canonicalDeterminant k,
    U,hU,hne,hcl,hsm⟩

/-- Arithmetic conversion to the advertised n²−5n+12 formula. -/
theorem component_dimension_formula (k : ℕ) (hk : 1 ≤ k) :
    k^2+3*k+8 = (k+4)^2-5*(k+4)+12 := by
  have h : 5*(k+4) ≤ (k+4)^2 := by nlinarith
  have he : (k+4)^2+12 = 5*(k+4)+(k^2+3*k+8) := by ring
  omega

#print axioms full_component_exists
#print full_component_exists
end
end ComponentCanonicalProblem
