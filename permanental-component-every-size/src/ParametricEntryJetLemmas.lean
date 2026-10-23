import ParametricEntryJetVector
import EntryJetLemmas

namespace ParametricLocalGeometry
open ConcreteLocalGeometry

@[simp] theorem evalOrigin_translatedN (s : ℂ) (r c : Fin 5) :
    evalOrigin (translatedN s r c) = parametricEntryJetTable s r c 0 := by
  simpa [entryJet] using parametric_entryJet_provenance s r c 0

@[simp] theorem firstDerivative_translatedN (s : ℂ) (i : Fin 16) (r c : Fin 5) :
    firstDerivative i (translatedN s r c) = parametricEntryJetTable s r c (jetFirstSlot i) := by
  have h := parametric_entryJet_provenance s r c (jetFirstSlot i)
  fin_cases i <;> simpa [jetFirstSlot,entryJet] using h

@[simp] theorem secondDerivative12_translatedN (s : ℂ) (r c : Fin 5) :
    secondDerivative 1 2 (translatedN s r c) = parametricEntryJetTable s r c 17 := by
  simpa [entryJet] using parametric_entryJet_provenance s r c 17

@[simp] theorem secondDerivative13_translatedN (s : ℂ) (r c : Fin 5) :
    secondDerivative 1 3 (translatedN s r c) = parametricEntryJetTable s r c 18 := by
  simpa [entryJet] using parametric_entryJet_provenance s r c 18

@[simp] theorem secondDerivative23_translatedN (s : ℂ) (r c : Fin 5) :
    secondDerivative 2 3 (translatedN s r c) = parametricEntryJetTable s r c 19 := by
  simpa [entryJet] using parametric_entryJet_provenance s r c 19

end ParametricLocalGeometry
