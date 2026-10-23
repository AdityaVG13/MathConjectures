import CriticalContainment
import EquationIndex
import GeneratorExponents
import MonomialBridge
namespace ConcreteLocalGeometry


theorem flatEquation_support (k : Fin 25) (d : Fin 16 →₀ ℕ)
    (hd : d ∈ (flatEquation k).support) : ∃ i, generatorExponent i ≤ d := by
  have hmem : flatEquation k ∈ targetIdeal := by
    simpa [flatEquation] using equation_mem_target (equationPair k).1 (equationPair k).2
  rw [targetIdeal_eq_monomialIdeal] at hmem
  exact (LocalGeometryMonomial.mem_monomialIdeal_iff generatorExponent (flatEquation k)).mp hmem d hd
#print axioms flatEquation_support
end ConcreteLocalGeometry
