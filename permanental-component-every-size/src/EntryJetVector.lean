import JetEvaluation
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace ConcreteLocalGeometry
/-- Literal emath035 data, not a proof of correspondence. -/
def entryJetTable : Fin 5 → Fin 5 → Fin 20 → ℂ :=
  ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![10, 9, 10, 20, -4, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 20, -4, -8], ![0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 6, -4], ![10, 9, 10, 10, -4, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 50, -4, -4], ![5, 2, -15, 10, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -30, 6, -4], ![5, 2, -15, 10, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -30, 6, -4]], ![![10, 9, -30, 20, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -60, 12, -8], ![0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 6, -4], ![10, 9, -30, 10, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, -30, 12, -4], ![5, 2, -15, 10, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -30, 6, -4], ![-5, -2, 15, -10, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 30, -6, 4]]]

noncomputable def entryJet (k : Fin 20) (f : P) : ℂ :=
  ![evalOrigin f, firstDerivative 0 f, firstDerivative 1 f,
    firstDerivative 2 f, firstDerivative 3 f, firstDerivative 4 f,
    firstDerivative 5 f, firstDerivative 6 f, firstDerivative 7 f,
    firstDerivative 8 f, firstDerivative 9 f, firstDerivative 10 f,
    firstDerivative 11 f, firstDerivative 12 f, firstDerivative 13 f,
    firstDerivative 14 f, firstDerivative 15 f,
    secondDerivative 1 2 f, secondDerivative 1 3 f, secondDerivative 2 3 f] k

theorem entryJet_vector_provenance (r c : Fin 5) :
    (fun k => entryJet k (N r c)) = entryJetTable r c := by
  fin_cases r <;> fin_cases c
  all_goals norm_num [entryJet,entryJetTable,N,jn,kn,zn,den,da,dq,dd,t,x,evalOrigin]

theorem entryJet_provenance (r c : Fin 5) (k : Fin 20) :
    entryJet k (N r c) = entryJetTable r c k :=
  congrFun (entryJet_vector_provenance r c) k
#print axioms entryJet_provenance
end ConcreteLocalGeometry
