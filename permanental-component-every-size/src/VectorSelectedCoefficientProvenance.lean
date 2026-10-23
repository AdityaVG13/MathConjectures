import EntryJetLemmas
import JetCoefficient
import EquationIndex
import CoefficientDataComplex
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace ConcreteLocalGeometry
open PrimitiveFamily LocalGeometryRank

theorem selected_coefficient_vector (i : Fin 15) :
    (fun j => jetCoefficient j (flatEquation (selectedRows i))) = coefficientDataComplex (selectedRows i) := by
  fin_cases i
  all_goals simp only [jetCoefficient,flatEquation,selectedRows,equationPair,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  all_goals unfold equation
  all_goals simp only [expand4]
  all_goals norm_num [Fin.sum_univ_succ,Fin.prod_univ_succ,enumerate4,
    p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,
    Matrix.submatrix,Fin.succAbove,entryJetTable,jetFirstSlot,coefficientDataComplex]
  all_goals rfl
theorem selected_coefficient_provenance (i j : Fin 15) :
    jetCoefficient j (flatEquation (selectedRows i)) = selectedMatrixComplex i j := by
  rw [selectedMatrixComplex_eq_data]
  exact congrFun (selected_coefficient_vector i) j
#print axioms selected_coefficient_provenance
end ConcreteLocalGeometry
