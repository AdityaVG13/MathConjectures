import GlobalIdealSetup
import VectorSelectedCoefficientProvenance
import LocalAssembly

/-! Exact local ideal equality for the denominator-cleared sixteen-variable slice.
This theorem does not assert the additional twenty-five-variable torus-chart
isomorphism, component dimensions, or historical novelty. -/
namespace ConcreteLocalGeometry
open LocalGeometryRank

theorem actual_selected_coefficient_matrix :
    LocalGeometryMonomial.coefficientMatrix generatorExponent
      (flatEquation ∘ selectedRows) = selectedMatrixComplex := by
  ext i j
  change (flatEquation (selectedRows i)).coeff (generatorExponent j) = selectedMatrixComplex i j
  rw [← jetCoefficient_eq_coeff j (flatEquation (selectedRows i))]
  exact selected_coefficient_provenance i j

theorem targetIdeal_generation :
    targetIdeal = criticalIdeal ⊔ MvPolynomial.idealOfVars (Fin 16) ℂ * targetIdeal := by
  have hinverse : inverseMatrixComplex *
      LocalGeometryMonomial.coefficientMatrix generatorExponent
        (flatEquation ∘ selectedRows) = 1 := by
    rw [actual_selected_coefficient_matrix]
    exact inverse_mul_selected_complex
  have h := LocalGeometryMonomial.monomialIdeal_eq_span_sup_vars_mul_of_selected_leftInverse
    generatorExponent generatorExponent_injective flatEquation flatEquation_support
    selectedRows inverseMatrixComplex hinverse
  rw [← targetIdeal_eq_monomialIdeal, flatEquation_range] at h
  simpa only [criticalIdeal] using h

/-- Unconditional equality of the actual localized ideals, not merely their
radicals, zero sets, or truncated jets. -/
theorem localCritical_eq_localTarget : localCritical = localTarget :=
  localCritical_eq_localTarget_of_global_certificate criticalIdeal_le_targetIdeal targetIdeal_generation

#print axioms actual_selected_coefficient_matrix
#print axioms targetIdeal_generation
#print axioms localCritical_eq_localTarget
end ConcreteLocalGeometry
