import GeometryBridge.IntegralDimension
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

namespace UniformComponentGeometry
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Going down over a domain forces every minimal prime to lie over zero. -/
theorem minimalPrime_under_eq_bot [IsDomain R] [Algebra.HasGoingDown R S]
    (Q : Ideal S) (hQ : IsMinimalPrime Q) : Q.under R = ⊥ := by
  letI : Q.IsPrime := hQ.isPrime
  obtain ⟨P, hPQ, hP, hPover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal R))
      (q := Q.under R) Q bot_le
  have heq : P = Q := le_antisymm hPQ (hQ.2 ⟨hP, bot_le⟩ hPQ)
  subst P
  exact hPover.over.symm

/-- Each minimal-prime quotient of a flat integral algebra over a domain has
exactly the dimension of the base, without an irreducibility assumption on the algebra. -/
theorem ringKrullDim_minimalPrime_quotient [IsDomain R] [Module.Flat R S]
    [Algebra.IsIntegral R S] (Q : Ideal S) (hQ : IsMinimalPrime Q) :
    ringKrullDim (S ⧸ Q) = ringKrullDim R := by
  have hc := minimalPrime_under_eq_bot (R := R) Q hQ
  apply ringKrullDim_eq_of_integral_injective (R := R)
  apply (injective_iff_map_eq_zero _).mpr
  intro r hr
  have hm : algebraMap R S r ∈ Q := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp hr
  have : r ∈ Q.under R := hm
  simpa [hc] using this

/-- Every prime point of a flat integral chart lies on a minimal-prime component
whose quotient has the dimension of the base. -/
theorem exists_minimalPrime_le_with_dimension [IsDomain R] [Module.Flat R S]
    [Algebra.IsIntegral R S] (P : Ideal S) [P.IsPrime] :
    ∃ Q : Ideal S, IsMinimalPrime Q ∧ Q ≤ P ∧
      ringKrullDim (S ⧸ Q) = ringKrullDim R := by
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S))
    (J := P) bot_le
  exact ⟨Q, hQ, hQP, ringKrullDim_minimalPrime_quotient (R := R) Q hQ⟩

#print axioms exists_minimalPrime_le_with_dimension
#print axioms minimalPrime_under_eq_bot
#print axioms ringKrullDim_minimalPrime_quotient
end UniformComponentGeometry
