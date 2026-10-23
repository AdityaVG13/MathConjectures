import ConcreteLocalSetup

/-! The actual fifteen monomial exponents, in the certificate's column order. -/
namespace ConcreteLocalGeometry

noncomputable def generatorExponent : Fin 15 → (Fin 16 →₀ ℕ) :=
  ![Finsupp.single 4 1, Finsupp.single 5 1, Finsupp.single 6 1,
    Finsupp.single 7 1, Finsupp.single 8 1, Finsupp.single 9 1,
    Finsupp.single 10 1, Finsupp.single 11 1, Finsupp.single 12 1,
    Finsupp.single 13 1, Finsupp.single 14 1, Finsupp.single 15 1,
    Finsupp.single 1 1 + Finsupp.single 2 1,
    Finsupp.single 1 1 + Finsupp.single 3 1,
    Finsupp.single 2 1 + Finsupp.single 3 1]

/-- A computable coordinate table used only to check that the exponents differ. -/
private def exponentValues : Fin 15 → (Fin 16 → ℕ) :=
  ![Pi.single 4 1, Pi.single 5 1, Pi.single 6 1,
    Pi.single 7 1, Pi.single 8 1, Pi.single 9 1,
    Pi.single 10 1, Pi.single 11 1, Pi.single 12 1,
    Pi.single 13 1, Pi.single 14 1, Pi.single 15 1,
    Pi.single 1 1 + Pi.single 2 1,
    Pi.single 1 1 + Pi.single 3 1,
    Pi.single 2 1 + Pi.single 3 1]

theorem generatorExponent_injective : Function.Injective generatorExponent := by
  have hvalues (i : Fin 15) : (generatorExponent i : Fin 16 → ℕ) = exponentValues i := by
    fin_cases i <;> simp [generatorExponent, exponentValues, Finsupp.single_eq_pi_single]
  have hinj : Function.Injective exponentValues := by decide +kernel
  intro i j hij
  apply hinj
  rw [← hvalues i, ← hvalues j, hij]
/-- Identification with the generators used in the actual target ideal. -/
theorem targetGenerator_eq_monomial (i : Fin 15) :
    targetGenerator i = MvPolynomial.monomial (generatorExponent i) (1 : ℂ) := by
  fin_cases i <;>
    simp [targetGenerator, generatorExponent, x, MvPolynomial.X,
      MvPolynomial.monomial_mul_monomial]

end ConcreteLocalGeometry

#print axioms ConcreteLocalGeometry.generatorExponent_injective
#print axioms ConcreteLocalGeometry.targetGenerator_eq_monomial
