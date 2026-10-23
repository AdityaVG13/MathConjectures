import ParametricEntryJetLemmas
import JetCoefficient
import EquationIndex
import PolynomialCertificateData
import MonomialBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-!
Symbolic provenance of the selected coefficient matrix, for the actual translated
permanent equations. The parameter remains arbitrary throughout. This file
uses no evaluation samples, rank hypothesis, or truncated-ideal membership claim.
-/
namespace ParametricLocalGeometry
open ConcreteLocalGeometry PrimitiveFamily LocalGeometryRank

noncomputable def translatedFlatEquation (s : ℂ) (k : Fin 25) : P :=
  translatedEquation s (equationPair k)

theorem translatedFlatEquation_eq_translation (s : ℂ) (k : Fin 25) :
    translatedFlatEquation s k = translation s (flatEquation k) := by
  exact translatedEquation_eq_translation s (equationPair k)

theorem translatedFlatEquation_range (s : ℂ) :
    Set.range (translatedFlatEquation s) = Set.range (translatedEquation s) :=
  equationPair_surjective.range_comp (translatedEquation s)

theorem selected_coefficient_vector (s : ℂ) (i : Fin 15) :
    (fun j => jetCoefficient j (translatedFlatEquation s (selectedRows i))) =
      PolynomialFamilyCertificate.coefficientMatrix s (selectedRows i) := by
  fin_cases i
  all_goals simp only [jetCoefficient,translatedFlatEquation,selectedRows,equationPair,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  all_goals unfold translatedEquation
  all_goals simp only [expand4]
  all_goals norm_num [Fin.sum_univ_succ,Fin.prod_univ_succ,enumerate4,
    p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,
    Matrix.submatrix,Fin.succAbove,parametricEntryJetTable,jetFirstSlot,
    PolynomialFamilyCertificate.coefficientMatrix]
  all_goals repeat' constructor
  all_goals ring

theorem selected_jet_coefficient_provenance (s : ℂ) (i j : Fin 15) :
    jetCoefficient j (translatedFlatEquation s (selectedRows i)) =
      PolynomialFamilyCertificate.selectedMatrix s i j := by
  exact congrFun (selected_coefficient_vector s i) j

theorem selected_coefficient_provenance (s : ℂ) (i j : Fin 15) :
    (translatedFlatEquation s (selectedRows i)).coeff (generatorExponent j) =
      PolynomialFamilyCertificate.selectedMatrix s i j := by
  rw [← jetCoefficient_eq_coeff]
  exact selected_jet_coefficient_provenance s i j

theorem actual_selected_coefficient_matrix (s : ℂ) :
    LocalGeometryMonomial.coefficientMatrix generatorExponent
      (translatedFlatEquation s ∘ selectedRows) =
      PolynomialFamilyCertificate.selectedMatrix s := by
  ext i j
  exact selected_coefficient_provenance s i j

end ParametricLocalGeometry

#print axioms ParametricLocalGeometry.selected_coefficient_vector
#print axioms ParametricLocalGeometry.selected_jet_coefficient_provenance
#print axioms ParametricLocalGeometry.selected_coefficient_provenance

#print axioms ParametricLocalGeometry.actual_selected_coefficient_matrix
