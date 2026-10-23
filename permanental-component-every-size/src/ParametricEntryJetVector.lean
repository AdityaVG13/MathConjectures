import ParametricMatrix
import EntryJetVector
import ParametricEntryJetData

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-!
The literal symbolic entry-jet data is transcribed from emath experiment 045.
The theorem below independently verifies it on the translated actual matrix
using universal polynomial derivative identities and symbolic ring arithmetic.
-/
namespace ParametricLocalGeometry
open ConcreteLocalGeometry

theorem parametric_entryJet_vector_provenance (s : ℂ) (r c : Fin 5) :
    (fun k => entryJet k (translatedN s r c)) = parametricEntryJetTable s r c := by
  rw [translatedN_eq_matrixWithParameter]
  fin_cases r <;> fin_cases c
  all_goals norm_num [entryJet,parametricEntryJetTable,matrixWithParameter,x,evalOrigin]
  all_goals repeat' constructor
  all_goals ring

theorem parametric_entryJet_provenance (s : ℂ) (r c : Fin 5) (k : Fin 20) :
    entryJet k (translatedN s r c) = parametricEntryJetTable s r c k :=
  congrFun (parametric_entryJet_vector_provenance s r c) k

end ParametricLocalGeometry

#print axioms ParametricLocalGeometry.parametric_entryJet_vector_provenance
#print axioms ParametricLocalGeometry.parametric_entryJet_provenance
