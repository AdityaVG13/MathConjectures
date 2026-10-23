import CanonicalProblem.SeedComponent

set_option autoImplicit false
namespace ComponentCanonicalProblem

/-- Every requested matrix size n≥5 corresponds to k=n-4≥1. -/
theorem parameter_positive (n : ℕ) (hn : 5 ≤ n) : 1 ≤ n-4 := by omega

theorem canonical_size (n : ℕ) (hn : 5 ≤ n) : 3+(n-4)+1 = n := by omega

/-- The canonical component dimension in the original matrix-size notation. -/
theorem canonical_dimension (n : ℕ) (hn : 5 ≤ n) :
    (n-4)^2 + 3*(n-4) + 8 = n^2 - 5*n + 12 := by
  have hs : n-4+4 = n := Nat.sub_add_cancel (by omega)
  have hq : 5*n ≤ n^2 := by nlinarith
  have ht := Nat.sub_add_cancel hq
  nlinarith

/-- Exact index-set equality, not an asymptotic or cardinality-only assertion.
Rewriting the canonical definitions along this equality gives independent
entries indexed literally by Fin n × Fin n. -/
def canonicalSizeEquiv (n : ℕ) (hn : 5 ≤ n) :
    Fin (3+(n-4)+1) ≃ Fin n := finCongr (canonical_size n hn)

#print axioms canonical_dimension
end ComponentCanonicalProblem
