import BChartEntryJetVector
import EntryJetLemmas

namespace BChartLocalGeometry
open ConcreteLocalGeometry

@[simp] theorem evalOrigin_matrixAt (s : ℂ) (r c : Fin 5) :
    evalOrigin (matrixAt s r c) = bchartEntryJetTable s r c 0 := by
  simpa [entryJet] using bchart_entryJet_provenance s r c 0

@[simp] theorem firstDerivative_matrixAt (s : ℂ) (i : Fin 16) (r c : Fin 5) :
    firstDerivative i (matrixAt s r c) = bchartEntryJetTable s r c (jetFirstSlot i) := by
  have h := bchart_entryJet_provenance s r c (jetFirstSlot i)
  fin_cases i <;> simpa [jetFirstSlot,entryJet] using h

@[simp] theorem secondDerivative12_matrixAt (s : ℂ) (r c : Fin 5) :
    secondDerivative 1 2 (matrixAt s r c) = bchartEntryJetTable s r c 17 := by
  simpa [entryJet] using bchart_entryJet_provenance s r c 17

@[simp] theorem secondDerivative13_matrixAt (s : ℂ) (r c : Fin 5) :
    secondDerivative 1 3 (matrixAt s r c) = bchartEntryJetTable s r c 18 := by
  simpa [entryJet] using bchart_entryJet_provenance s r c 18

@[simp] theorem secondDerivative23_matrixAt (s : ℂ) (r c : Fin 5) :
    secondDerivative 2 3 (matrixAt s r c) = bchartEntryJetTable s r c 19 := by
  simpa [entryJet] using bchart_entryJet_provenance s r c 19

end BChartLocalGeometry
