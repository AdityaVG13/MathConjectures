import GeometryBridge.InvertibleGenerators
import GeometryBridge.CoefficientLeftInverse
import GeometryBridge.CoefficientJacobian

namespace UniformComponentGeometry

variable {K R S ι κ : Type*} [Field K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra R S] [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

attribute [local instance] RingHom.ker_isPrime

/-- Exact coefficient identities whose evaluated coefficient matrix is injective give equality
of the entire localized ideals. The residue-field left inverse is lifted using constants;
no selected square minor or unproved geometric criterion is used. -/
theorem localized_ideal_eq_of_eval_coefficient_injective
    (ev : R →ₐ[K] K) [IsLocalization.AtPrime S (RingHom.ker ev.toRingHom)]
    (I : Ideal R) (A : Matrix ι κ R) (g : κ → R) (f : ι → R)
    (hcontain : I ≤ Ideal.span (Set.range g)) (hselected : ∀ i, f i ∈ I)
    (hfg : f = A.mulVec g) (hinj : Function.Injective (A.map ev).mulVec) :
    I.map (algebraMap R S) = (Ideal.span (Set.range g)).map (algebraMap R S) := by
  obtain ⟨B₀, hB₀⟩ := exists_matrix_left_inverse_of_injective (A.map ev) hinj
  let B : Matrix κ ι R := B₀.map (algebraMap K R)
  have hB : B.map ev = B₀ := by
    ext i j
    simp [B, Matrix.map_apply]
  have hBA : (B * A).map ev = 1 := by
    rw [Matrix.map_mul, hB, hB₀]
  have hdet : ((B * A).map ev.toRingHom).det ≠ 0 := by
    change ((B * A).map ev).det ≠ 0
    rw [hBA, Matrix.det_one]
    exact one_ne_zero
  have hunit : IsUnit (((B * A).map (algebraMap R S)).det) :=
    isUnit_localized_det_of_eval_ne_zero ev.toRingHom (B * A) hdet
  have hunit' : IsUnit ((B.map (algebraMap R S) * A.map (algebraMap R S)).det) := by
    simpa only [Matrix.map_mul] using hunit
  obtain ⟨C, hC⟩ := exists_matrix_left_inverse_of_isUnit_product_det
    (A.map (algebraMap R S)) (B.map (algebraMap R S)) hunit'
  have hv : (fun i => algebraMap R S (f i)) =
      (A.map (algebraMap R S)).mulVec (fun i => algebraMap R S (g i)) := by
    funext i
    rw [hfg, RingHom.map_mulVec]
    rfl
  have he : (Ideal.span (Set.range f)).map (algebraMap R S) =
      (Ideal.span (Set.range g)).map (algebraMap R S) := by
    simp only [Ideal.map_span, ← Set.range_comp, Function.comp_def]
    rw [hv]
    exact span_mulVec_eq_of_left_inverse _ C hC _
  apply le_antisymm (Ideal.map_mono hcontain)
  rw [← he]
  apply Ideal.map_mono
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact hselected i

/-- Specialization to actual polynomial equations: exact membership certificates and full
Jacobian rank at their common zero identify the localized ideals. The rank is that of the
actual evaluated partial derivatives, not an auxiliary matrix. -/
theorem localized_polynomial_ideal_eq_of_jacobian_rank
    {ν : Type*} [Fintype ν] (x : ν → K)
    [Algebra (MvPolynomial ν K) S]
    [IsLocalization.AtPrime S (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)]
    (I : Ideal (MvPolynomial ν K)) (A : Matrix ι κ (MvPolynomial ν K))
    (g : κ → MvPolynomial ν K) (f : ι → MvPolynomial ν K)
    (hcontain : I ≤ Ideal.span (Set.range g)) (hselected : ∀ i, f i ∈ I)
    (hfg : f = A.mulVec g) (hg : ∀ j, MvPolynomial.eval x (g j) = 0)
    (hrank : (Matrix.of (fun i k => MvPolynomial.eval x
      (MvPolynomial.pderiv k (f i)))).rank = Fintype.card κ) :
    I.map (algebraMap (MvPolynomial ν K) S) =
      (Ideal.span (Set.range g)).map (algebraMap (MvPolynomial ν K) S) := by
  apply localized_ideal_eq_of_eval_coefficient_injective
    (MvPolynomial.aeval x) I A g f hcontain hselected hfg
  have hj := eval_jacobian_of_coefficient_identities x A f g hfg hg
  have hr : ((A.map (MvPolynomial.eval x)) * Matrix.of
      (fun j k => MvPolynomial.eval x (MvPolynomial.pderiv k (g j)))).rank =
      Fintype.card κ := by
    rw [← hj]
    exact hrank
  exact coefficient_injective_of_product_rank _ _ hr

#print axioms localized_ideal_eq_of_eval_coefficient_injective
#print axioms localized_polynomial_ideal_eq_of_jacobian_rank
end UniformComponentGeometry
