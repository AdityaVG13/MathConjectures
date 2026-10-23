import EntryJetVector
namespace ConcreteLocalGeometry

def jetFirstSlot (i : Fin 16) : Fin 20 := ⟨i.val+1, by omega⟩
@[simp] theorem evalOrigin_N (r c : Fin 5) :
    evalOrigin (N r c) = entryJetTable r c 0 := by
  simpa [entryJet] using entryJet_provenance r c 0
@[simp] theorem firstDerivative_N (i : Fin 16) (r c : Fin 5) :
    firstDerivative i (N r c) = entryJetTable r c (jetFirstSlot i) := by
  have h := entryJet_provenance r c (jetFirstSlot i)
  fin_cases i <;> simpa [jetFirstSlot,entryJet] using h
@[simp] theorem secondDerivative12_N (r c : Fin 5) :
    secondDerivative 1 2 (N r c) = entryJetTable r c 17 := by
  simpa [entryJet] using entryJet_provenance r c 17
@[simp] theorem secondDerivative13_N (r c : Fin 5) :
    secondDerivative 1 3 (N r c) = entryJetTable r c 18 := by
  simpa [entryJet] using entryJet_provenance r c 18
@[simp] theorem secondDerivative23_N (r c : Fin 5) :
    secondDerivative 2 3 (N r c) = entryJetTable r c 19 := by
  simpa [entryJet] using entryJet_provenance r c 19
end ConcreteLocalGeometry
