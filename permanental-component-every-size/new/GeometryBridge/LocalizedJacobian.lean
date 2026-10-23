import GeometryBridge.EvaluatedIdealEquality
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace UniformComponentGeometry
noncomputable section
attribute [local instance] RingHom.ker_isPrime

/-- Actual local ideal membership supplies a polynomial denominator nonvanishing at the point. -/
theorem exists_denominator_of_local_mem
    {R K S : Type*} [CommRing R] [Field K] [CommRing S] [Algebra R S]
    (ev : R →+* K) [IsLocalization.AtPrime S (RingHom.ker ev)]
    (J : Ideal R) (f : R) (hf : algebraMap R S f ∈ J.map (algebraMap R S)) :
    ∃ s : R, ev s ≠ 0 ∧ s*f ∈ J := by
  obtain ⟨s, hs, hsf⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (RingHom.ker ev).primeCompl S J f).mp hf
  exact ⟨s, hs, hsf⟩

/-- Family form matching denominator-cleared Jacobian rank bounds. -/
theorem denominators_of_local_membership
    {R K S ι : Type*} [CommRing R] [Field K] [CommRing S] [Algebra R S]
    (ev : R →+* K) [IsLocalization.AtPrime S (RingHom.ker ev)]
    (J : Ideal R) (f : ι → R)
    (hf : ∀ i, algebraMap R S (f i) ∈ J.map (algebraMap R S)) :
    ∀ i, ∃ s : R, ev s ≠ 0 ∧ s*f i ∈ J :=
  fun i => exists_denominator_of_local_mem ev J (f i) (hf i)

variable {K S ν ι κ : Type*} [Field K] [CommRing S]
  [Fintype ν] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Algebra (MvPolynomial ν K) S]

/-- A polynomial in the localized span of equations vanishing at x also vanishes at x. -/
theorem eval_eq_zero_of_local_span_membership (x : ν → K)
    [IsLocalization.AtPrime S (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)]
    (g : κ → MvPolynomial ν K) (f : MvPolynomial ν K)
    (hg : ∀ j, MvPolynomial.eval x (g j) = 0)
    (hf : algebraMap (MvPolynomial ν K) S f ∈
      (Ideal.span (Set.range g)).map (algebraMap (MvPolynomial ν K) S)) :
    MvPolynomial.eval x f = 0 := by
  obtain ⟨s, hs, hsf⟩ := exists_denominator_of_local_mem
    (MvPolynomial.aeval (R := K) x).toRingHom (Ideal.span (Set.range g)) f hf
  have hk : Ideal.span (Set.range g) ≤ RingHom.ker (MvPolynomial.eval x) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hg j
  have hz : MvPolynomial.eval x (s*f) = 0 := hk hsf
  rw [map_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left hs

/-- Multiplication by denominators nonzero at a common zero preserves actual Jacobian rank. -/
theorem jacobian_rank_mul_denominators (x : ν → K)
    (s f : ι → MvPolynomial ν K)
    (hs : ∀ i, MvPolynomial.eval x (s i) ≠ 0)
    (hf : ∀ i, MvPolynomial.eval x (f i) = 0) :
    (Matrix.of (fun i k => MvPolynomial.eval x (MvPolynomial.pderiv k (s i*f i)))).rank =
      (Matrix.of (fun i k => MvPolynomial.eval x (MvPolynomial.pderiv k (f i)))).rank := by
  have he : Matrix.of (fun i k => MvPolynomial.eval x (MvPolynomial.pderiv k (s i*f i))) =
      Matrix.diagonal (fun i => MvPolynomial.eval x (s i)) *
        Matrix.of (fun i k => MvPolynomial.eval x (MvPolynomial.pderiv k (f i))) := by
    ext i k
    simp [MvPolynomial.pderiv_mul, hf, Matrix.diagonal_mul]
  rw [he]
  apply Matrix.rank_mul_eq_right_of_det_ne_zero
  simpa [Matrix.det_diagonal] using Finset.prod_ne_zero_iff.mpr (fun i _ => hs i)

/-- Full rank identifies the localized actual ideal even when containment is known only
locally. No global membership of the unscaled equations is assumed. -/
theorem localized_polynomial_ideal_eq_of_local_containment
    (x : ν → K)
    [IsLocalization.AtPrime S (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)]
    (I : Ideal (MvPolynomial ν K)) (g : κ → MvPolynomial ν K)
    (f : ι → MvPolynomial ν K)
    (hlocal : I.map (algebraMap (MvPolynomial ν K) S) ≤
      (Ideal.span (Set.range g)).map (algebraMap (MvPolynomial ν K) S))
    (hselected : ∀ i, f i ∈ I)
    (hg : ∀ j, MvPolynomial.eval x (g j) = 0)
    (hrank : (Matrix.of (fun i k => MvPolynomial.eval x
      (MvPolynomial.pderiv k (f i)))).rank = Fintype.card κ) :
    I.map (algebraMap (MvPolynomial ν K) S) =
      (Ideal.span (Set.range g)).map (algebraMap (MvPolynomial ν K) S) := by
  have hf : ∀ i, MvPolynomial.eval x (f i) = 0 := fun i =>
    eval_eq_zero_of_local_span_membership (S := S) x g (f i) hg
      (hlocal (Ideal.mem_map_of_mem _ (hselected i)))
  have hd := denominators_of_local_membership (MvPolynomial.aeval (R := K) x).toRingHom
    (Ideal.span (Set.range g)) f
    (fun i => hlocal (Ideal.mem_map_of_mem _ (hselected i)))
  choose s hs hsg using hd
  have hex : ∀ i, ∃ a : κ → MvPolynomial ν K, ∑ j, a j * g j = s i * f i := by
    intro i
    exact (Submodule.mem_span_range_iff_exists_fun (MvPolynomial ν K)).mp (hsg i)
  choose A hA using hex
  let f' : ι → MvPolynomial ν K := fun i => s i * f i
  let I' : Ideal (MvPolynomial ν K) := Ideal.span (Set.range f')
  have hfg : f' = (Matrix.of A).mulVec g := by
    funext i
    exact (hA i).symm
  have hcontain : I' ≤ Ideal.span (Set.range g) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hsg i
  have hrank' : (Matrix.of (fun i k => MvPolynomial.eval x
      (MvPolynomial.pderiv k (f' i)))).rank = Fintype.card κ := by
    rw [jacobian_rank_mul_denominators x s f hs hf, hrank]
  have he := localized_polynomial_ideal_eq_of_jacobian_rank (S := S)
    x I' (Matrix.of A) g f' hcontain (fun i => Ideal.mem_span_range_self) hfg hg hrank'
  apply le_antisymm hlocal
  rw [← he]
  apply Ideal.map_mono
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact I.mul_mem_left (s i) (hselected i)

#print axioms exists_denominator_of_local_mem
#print axioms localized_polynomial_ideal_eq_of_local_containment
end
end UniformComponentGeometry
