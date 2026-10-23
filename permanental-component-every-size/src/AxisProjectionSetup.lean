import ConcreteLocalSetup
namespace ConcreteLocalGeometry
noncomputable def axisProjection (k : Fin 16) : P →+* P :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => if i = 0 ∨ i = k then x i else 0)
end ConcreteLocalGeometry
