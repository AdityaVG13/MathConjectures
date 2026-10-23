import JetEvaluation
import GeneratorExponents
namespace ConcreteLocalGeometry
open MvPolynomial
noncomputable def jetCoefficient (j : Fin 15) (f : P) : ℂ :=
  ![firstDerivative 4 f,firstDerivative 5 f,firstDerivative 6 f,
    firstDerivative 7 f,firstDerivative 8 f,firstDerivative 9 f,
    firstDerivative 10 f,firstDerivative 11 f,firstDerivative 12 f,
    firstDerivative 13 f,firstDerivative 14 f,firstDerivative 15 f,
    secondDerivative 1 2 f,secondDerivative 1 3 f,secondDerivative 2 3 f] j

theorem jetCoefficient_eq_coeff (j : Fin 15) (f : P) :
    jetCoefficient j f = f.coeff (generatorExponent j) := by
  fin_cases j <;> simp [jetCoefficient,firstDerivative,secondDerivative,evalOrigin,
    MvPolynomial.constantCoeff_eq,coeff_pderiv,generatorExponent,Finsupp.single_apply]
#print axioms jetCoefficient_eq_coeff
end ConcreteLocalGeometry
