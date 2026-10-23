import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Spectrum.Prime.Topology

namespace UniformComponentGeometry

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Integral extensions contract strict prime chains strictly. -/
theorem ringKrullDim_le_of_integral [Algebra.IsIntegral R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
  intro p q hpq
  exact Ideal.IsIntegral.under_lt_under hpq

/-- Lying-over and going-up lift all finite prime chains without shortening them. -/
theorem ringKrullDim_le_of_goingUp_surjective [Algebra.HasGoingUp R S]
    (hs : Function.Surjective (PrimeSpectrum.comap (algebraMap R S))) :
    ringKrullDim R ≤ ringKrullDim S := by
  unfold ringKrullDim Order.krullDim
  apply iSup_le
  intro l
  obtain ⟨P, hP⟩ := hs l.head
  have hPQ : P.asIdeal.LiesOver l.head.asIdeal := by
    constructor
    exact congrArg PrimeSpectrum.asIdeal hP.symm
  obtain ⟨L, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
  calc
    (l.length : WithBot ℕ∞) = L.length := by rw [hlen]
    _ ≤ ⨆ p : LTSeries (PrimeSpectrum S), (p.length : WithBot ℕ∞) := le_iSup (fun p : LTSeries (PrimeSpectrum S) => (p.length : WithBot ℕ∞)) L

/-- Krull dimension is preserved by every injective integral algebra extension. -/
theorem ringKrullDim_eq_of_integral_injective [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) : ringKrullDim S = ringKrullDim R := by
  letI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  exact le_antisymm ringKrullDim_le_of_integral
    (ringKrullDim_le_of_goingUp_surjective (Algebra.IsIntegral.comap_surjective R S))

omit [Algebra R S] in
/-- Ring-hom form, convenient for applying a proved Noether normalization map. -/
theorem ringKrullDim_eq_of_integral_ringHom
    (f : R →+* S) (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim S = ringKrullDim R := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra.IsIntegral R S := ⟨hf⟩
  exact ringKrullDim_eq_of_integral_injective hinj

/-- A concrete integral injection from an n-variable polynomial ring over a field certifies
actual Krull dimension n. This does not assert existence of such a map for a particular chart. -/
theorem ringKrullDim_eq_nat_of_integral_polynomial
    {K : Type*} [Field K] (n : ℕ) (f : MvPolynomial (Fin n) K →+* S)
    (hf : f.IsIntegral) (hinj : Function.Injective f) : ringKrullDim S = n := by
  rw [ringKrullDim_eq_of_integral_ringHom f hf hinj,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field]
  simp

#print axioms ringKrullDim_eq_of_integral_injective
#print axioms ringKrullDim_eq_nat_of_integral_polynomial
end UniformComponentGeometry
