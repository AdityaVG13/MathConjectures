import ConcreteLocalSetup
namespace ConcreteLocalGeometry
/-- Explicit row-major identification; there is no signed cofactor convention. -/
def equationPair : Fin 25 → Fin 5 × Fin 5 :=
  ![(0,0),(0,1),(0,2),(0,3),(0,4),
    (1,0),(1,1),(1,2),(1,3),(1,4),
    (2,0),(2,1),(2,2),(2,3),(2,4),
    (3,0),(3,1),(3,2),(3,3),(3,4),
    (4,0),(4,1),(4,2),(4,3),(4,4)]
theorem equationPair_surjective : Function.Surjective equationPair := by
  rintro ⟨r,c⟩
  refine ⟨⟨5*r.val+c.val, by omega⟩, ?_⟩
  fin_cases r <;> fin_cases c <;> rfl
noncomputable def flatEquation (k : Fin 25) : P := equation (equationPair k)
theorem flatEquation_range : Set.range flatEquation = Set.range equation := by
  exact equationPair_surjective.range_comp equation
end ConcreteLocalGeometry
