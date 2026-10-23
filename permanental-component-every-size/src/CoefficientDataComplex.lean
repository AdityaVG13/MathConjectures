import ComplexRank
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
namespace ConcreteLocalGeometry
def coefficientDataComplex : Matrix (Fin 25) (Fin 15) ℂ :=
  !![0, 0, -100, 0, 0, 0, 0, 25, 0, -25, 0, 25, 200, 20, 0;
     0, 0, 400, 0, 0, 0, 25, 0, -25, 0, 25, 0, -200, 0, 0;
     0, 0, -100, 0, 0, 0, 0, -25, 0, 25, 0, -25, 200, -20, 0;
     0, 0, -200, 0, 0, 0, -25, 0, 25, 0, -25, 0, -200, 0, 0;
     400, -100, 0, 0, 0, 0, 25, 0, -25, 0, -25, 0, -600, 0, 20;
     0, 0, 0, 0, 0, 100, 0, -50, 0, 50, 0, 0, 0, -20, 0;
     0, 0, 0, 0, 0, 400, -50, 0, -50, 0, 50, 250, -600, 200, 0;
     0, 0, 0, 0, 0, 100, 0, -50, 0, 50, 0, 0, 0, -20, 0;
     0, 0, 0, 0, 0, 200, 0, -50, 0, 50, 0, 0, 0, -360, 0;
     0, 0, 0, 100, 200, 0, 0, 250, 0, 250, 0, 0, 0, 80, -20;
     0, 0, 100, 0, 0, 0, 0, 25, 0, -25, 0, -25, -200, 20, 0;
     0, 0, 400, 0, 0, 0, 25, 0, -25, 0, 25, 0, -200, 0, 0;
     0, 0, 100, 0, 0, 0, 0, -25, 0, 25, 0, 25, -200, -20, 0;
     0, 0, 200, 0, 0, 0, 25, 0, -25, 0, 25, 0, 200, 0, 0;
     400, 100, 0, 0, 0, 0, -25, 0, 25, 0, 25, 0, 600, 0, 20;
     -10, 0, 0, 0, 5, -5, 0, 0, 0, 0, 0, 0, 0, -1, -5;
     0, -10, 50, -5, 0, 0, 0, 0, 0, 0, 0, 0, -10, 0, -5;
     -10, 0, 0, 0, -5, 5, 0, 0, 0, 0, 0, 0, 0, 1, -5;
     -10, 0, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5;
     50, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15;
     10, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, 0, -1, 5;
     0, 10, 50, 5, 0, 0, 0, 0, 0, 0, 0, 0, -10, 0, 5;
     10, 0, 0, 0, 5, 5, 0, 0, 0, 0, 0, 0, 0, 1, 5;
     10, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5;
     50, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15]

theorem selectedMatrixComplex_eq_data :
    LocalGeometryRank.selectedMatrixComplex = coefficientDataComplex.submatrix LocalGeometryRank.selectedRows id := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num [LocalGeometryRank.selectedMatrixComplex,LocalGeometryRank.selectedMatrix,
    LocalGeometryRank.coefficientMatrix,LocalGeometryRank.selectedRows,coefficientDataComplex,Matrix.map,Matrix.submatrix]
end ConcreteLocalGeometry
