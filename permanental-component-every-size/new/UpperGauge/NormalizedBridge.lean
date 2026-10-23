import UpperGauge.CofactorTransport
import GeometryBridge.NormalizedUpperEquiv
namespace UniformUpperGauge
noncomputable section
def interior : Fin 6 → Index := ![(1,3),(2,1),(1,1),(1,2),(2,2),(2,3)]
def normalizedCoordinates : UniformNormalizedUpper.Coordinates →+* A :=
  MvPolynomial.eval₂Hom ((algebraMap P A).comp MvPolynomial.C)
    (fun s => matrix (interior s).1 (interior s).2)

theorem normalizedMatrix_eq :
    normalized = UniformNormalizedUpper.normalizedMatrix.map normalizedCoordinates := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalized,IsPivot,UniformNormalizedUpper.normalizedMatrix,
      UniformNormalizedUpper.vars, normalizedCoordinates,interior,Matrix.map]

theorem normalizedCofactor_eq (c : Fin 4) :
    cofactor normalized c = normalizedCoordinates (UniformNormalizedUpper.actualCofactor c) := by
  rw [normalizedMatrix_eq]
  simp [cofactor,UniformNormalizedUpper.actualCofactor,Matrix.permanent,
    Matrix.submatrix,Matrix.map,map_sum,map_prod]

theorem normalizedIdeal_eq :
    cofactorIdeal normalized = Ideal.map normalizedCoordinates UniformNormalizedUpper.ideal := by
  rw [UniformNormalizedUpper.ideal_eq_actualCofactors]
  simp only [cofactorIdeal, Ideal.map_span, ← Set.range_comp]
  congr 2
  funext c
  exact normalizedCofactor_eq c

#print axioms normalizedIdeal_eq
end
end UniformUpperGauge
