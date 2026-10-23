import BChartSetup
import EntryJetVector
import BChartEntryJetData

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-!
The literal symbolic entry-jet data is transcribed from the exact emath b-chart entry-jet experiment.
The theorem below independently verifies it on the translated actual matrix
using universal polynomial derivative identities and symbolic ring arithmetic.
-/
namespace BChartLocalGeometry
open ConcreteLocalGeometry

@[simp] theorem firstDerivative_two (i : Fin 16) :
    firstDerivative i (2 : P) = 0 := by
  simpa only [map_ofNat] using first_C i (2 : ℂ)

@[simp] theorem secondDerivative_two (i j : Fin 16) :
    secondDerivative i j (2 : P) = 0 := by
  simpa only [map_ofNat] using second_C i j (2 : ℂ)

@[simp] theorem constantCoeff_two :
    MvPolynomial.constantCoeff (2 : P) = (2 : ℂ) := by
  simp only [map_ofNat]

theorem bchart_entryJet_vector_provenance (s : ℂ) (r c : Fin 5) :
    (fun k => entryJet k (matrixAt s r c)) = bchartEntryJetTable s r c := by
  fin_cases r <;> fin_cases c
  all_goals norm_num [entryJet,bchartEntryJetTable,matrixAt,matrixWithParameter,x,evalOrigin]
  all_goals repeat' constructor
  all_goals ring

theorem bchart_entryJet_provenance (s : ℂ) (r c : Fin 5) (k : Fin 20) :
    entryJet k (matrixAt s r c) = bchartEntryJetTable s r c k :=
  congrFun (bchart_entryJet_vector_provenance s r c) k

end BChartLocalGeometry

#print axioms BChartLocalGeometry.bchart_entryJet_vector_provenance
#print axioms BChartLocalGeometry.bchart_entryJet_provenance
