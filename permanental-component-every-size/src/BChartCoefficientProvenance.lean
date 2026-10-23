import BChartEntryJetLemmas
import JetCoefficient
import EquationIndex
import BChartCertificateRows
import MonomialBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-!
Symbolic provenance of the selected coefficient matrix, for the actual translated corrected b-chart
permanent equations. The parameter remains arbitrary throughout. This file
uses no evaluation samples, rank hypothesis, or truncated-ideal membership claim.
-/
namespace BChartLocalGeometry
open ConcreteLocalGeometry PrimitiveFamily LocalGeometryRank

noncomputable def flatEquation (s : ℂ) (k : Fin 25) : P :=
  equation s (equationPair k)

theorem flatEquation_range (s : ℂ) :
    Set.range (flatEquation s) = Set.range (equation s) :=
  equationPair_surjective.range_comp (equation s)

theorem selected_coefficient_vector (s : ℂ) (i : Fin 15) :
    (fun j => jetCoefficient j (flatEquation s (selectedRows i))) =
      BChartPolynomialCertificate.coefficientMatrix s (selectedRows i) := by
  fin_cases i
  all_goals simp only [jetCoefficient,flatEquation,selectedRows,equationPair,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  all_goals unfold equation
  all_goals simp only [expand4]
  all_goals norm_num [Fin.sum_univ_succ,Fin.prod_univ_succ,enumerate4,
    p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,
    Matrix.submatrix,Fin.succAbove,bchartEntryJetTable,jetFirstSlot,
    BChartPolynomialCertificate.coefficientMatrix]
  all_goals repeat' constructor
  all_goals ring

theorem selected_jet_coefficient_provenance (s : ℂ) (i j : Fin 15) :
    jetCoefficient j (flatEquation s (selectedRows i)) =
      BChartPolynomialCertificate.selectedMatrix s i j := by
  exact congrFun (selected_coefficient_vector s i) j

theorem selected_coefficient_provenance (s : ℂ) (i j : Fin 15) :
    (flatEquation s (selectedRows i)).coeff (generatorExponent j) =
      BChartPolynomialCertificate.selectedMatrix s i j := by
  rw [← jetCoefficient_eq_coeff]
  exact selected_jet_coefficient_provenance s i j

theorem actual_selected_coefficient_matrix (s : ℂ) :
    LocalGeometryMonomial.coefficientMatrix generatorExponent
      (flatEquation s ∘ selectedRows) =
      BChartPolynomialCertificate.selectedMatrix s := by
  ext i j
  exact selected_coefficient_provenance s i j

end BChartLocalGeometry

#print axioms BChartLocalGeometry.selected_coefficient_vector
#print axioms BChartLocalGeometry.selected_jet_coefficient_provenance
#print axioms BChartLocalGeometry.selected_coefficient_provenance

#print axioms BChartLocalGeometry.actual_selected_coefficient_matrix
