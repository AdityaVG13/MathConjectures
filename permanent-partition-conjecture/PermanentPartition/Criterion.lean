import PermanentPartition.Expansion
import PermanentPartition.Singular

/-!
# A criterion for refuting the conjecture

Suppose a complex matrix `B` lies in `Sing(P)`, but for every partition `(S, Sᶜ)` of its rows,
and for every partition of its columns, the maximal permanents of `B` on one of the two parts do
not all vanish. Then Conjecture 4.27 fails for that size (`not_conjecture_of_witness`).

The argument uses the kernel of evaluation at `B`, which is a prime ideal because `ℂ` is a
domain.

* The left-hand side `rad(I(Sing(P)))` is contained in the kernel, because `B ∈ Sing(P)`.
* For each partition, `J_{S₁} + J_{S₂}` is not contained in the kernel, because some maximal
  permanent on `S₁` or on `S₂` is nonzero at `B`. Since the kernel is prime, the same holds for
  the radical of `J_{S₁} + J_{S₂}`.
* A prime ideal that contains a finite intersection of ideals contains one of them. Hence the
  right-hand side is not contained in the kernel either, and the two sides differ.

No separating polynomial is written down; its existence follows from the argument.
-/

namespace PermanentPartition

variable {k : ℕ}

/-- All maximal permanents of `B` on the rows `S` vanish. -/
def Vanishes {α : Type*} [CommSemiring α] (B : Matrix (Fin k) (Fin k) α)
    (S : Finset (Fin k)) : Prop :=
  ∀ p ∈ maximalPermanents B S, p = 0

/-- `J_S` vanishes at `B` exactly when all maximal permanents of `B` on `S` vanish. -/
theorem J_le_ker_iff (B : Matrix (Fin k) (Fin k) ℂ) (column : Bool) (S : Finset (Fin k)) :
    J column S ≤ RingHom.ker (evaluate B) ↔ Vanishes (orient column B) S := by
  rw [J, Ideal.span_le]
  constructor
  · rintro h p ⟨m, r, c, hr, hc, hS, rfl⟩
    rw [← evaluate_permanent B column r c]
    exact RingHom.mem_ker.mp (h ⟨m, r, c, hr, hc, hS, rfl⟩)
  · rintro h p ⟨m, r, c, hr, hc, hS, rfl⟩
    apply RingHom.mem_ker.mpr
    rw [evaluate_permanent]
    exact h _ ⟨m, r, c, hr, hc, hS, rfl⟩

/-- The empty set of rows has the permanent of the empty matrix, which is `1`. -/
theorem not_vanishes_empty {α : Type*} [CommSemiring α] [Nontrivial α]
    (B : Matrix (Fin k) (Fin k) α) : ¬ Vanishes B ∅ := by
  intro h
  have h0 := h _ ⟨0, Fin.elim0, Fin.elim0, Function.injective_of_subsingleton _,
    Function.injective_of_subsingleton _, by simp, rfl⟩
  rw [Matrix.permanent_isEmpty] at h0
  exact one_ne_zero h0

/-- A single row with a nonzero entry. -/
theorem not_vanishes_singleton {α : Type*} [CommSemiring α] (B : Matrix (Fin k) (Fin k) α)
    {i j : Fin k} (h : B i j ≠ 0) : ¬ Vanishes B {i} := by
  intro hv
  apply h
  have h0 := hv _ ⟨1, fun _ => i, fun _ => j, Function.injective_of_subsingleton _,
    Function.injective_of_subsingleton _, by simp, rfl⟩
  simpa [Matrix.permanent_unique] using h0

/-- Two rows `i, j` and two columns `c, d` with a nonzero `2 × 2` permanent. -/
theorem not_vanishes_pair {α : Type*} [CommSemiring α] (B : Matrix (Fin k) (Fin k) α)
    {i j c d : Fin k} (hij : i ≠ j) (hcd : c ≠ d)
    (h : B i c * B j d + B i d * B j c ≠ 0) : ¬ Vanishes B {i, j} := by
  have hinj : ∀ {x y : Fin k}, x ≠ y → Function.Injective ![x, y] := by
    intro x y hxy a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  intro hv
  apply h
  have h0 := hv _ ⟨2, ![i, j], ![c, d], hinj hij, hinj hcd, by simp [Finset.univ_fin2], rfl⟩
  rw [permanent_succ_column_zero] at h0
  simpa [Fin.sum_univ_succ, Matrix.permanent_unique, add_comm, mul_comm] using h0

/-- If every row has a nonzero entry and every two rows have a nonzero `2 × 2` permanent, then no
nonempty set of at most two rows vanishes. -/
theorem not_vanishes_of_card_le_two {α : Type*} [CommSemiring α] (B : Matrix (Fin k) (Fin k) α)
    (h1 : ∀ i, ∃ j, B i j ≠ 0)
    (h2 : ∀ i j, i ≠ j → ∃ c d, c ≠ d ∧ B i c * B j d + B i d * B j c ≠ 0)
    (S : Finset (Fin k)) (hS : S.Nonempty) (hcard : S.card ≤ 2) : ¬ Vanishes B S := by
  have hpos := Finset.card_pos.mpr hS
  rcases (show S.card = 1 ∨ S.card = 2 by omega) with h | h
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h
    obtain ⟨j, hj⟩ := h1 i
    exact not_vanishes_singleton B hj
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp h
    obtain ⟨c, d, hcd, hp⟩ := h2 i j hij
    exact not_vanishes_pair B hij hcd hp
/-- If every nonempty set of at most two rows has a nonzero maximal permanent, then no partition
of the rows of a `5 × 5` matrix has both parts vanishing, since one part has at most two rows. -/
theorem no_partition_of_small {α : Type*} [CommSemiring α] (B : Matrix (Fin 5) (Fin 5) α)
    (h : ∀ S : Finset (Fin 5), S.Nonempty → S.card ≤ 2 → ¬ Vanishes B S)
    (S : Finset (Fin 5)) (hS : S.Nonempty) (hU : S ≠ Finset.univ) :
    ¬ (Vanishes B S ∧ Vanishes B Sᶜ) := by
  rintro ⟨h1, h2⟩
  have hcard : S.card + Sᶜ.card = 5 := by simp
  by_cases hsmall : S.card ≤ 2
  · exact h S hS hsmall h1
  · have hS' : Sᶜ.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr fun he => hU ((Finset.compl_eq_empty_iff S).mp he)
    exact h Sᶜ hS' (by omega) h2

/-- The main criterion: a matrix in `Sing(P)` with no partition of its rows or of its columns into
two vanishing parts refutes Conjecture 4.27. -/
theorem partitionIntersection_not_le_ker (B : Matrix (Fin k) (Fin k) ℂ)
    (hpart : ∀ (column : Bool) (S : Finset (Fin k)), S.Nonempty → S ≠ Finset.univ →
      ¬ (Vanishes (orient column B) S ∧ Vanishes (orient column B) Sᶜ)) :
    ¬ partitionIntersection k ≤ RingHom.ker (evaluate B) := by
  intro h
  rw [partitionIntersection, ← Finset.inf_univ_eq_iInf] at h
  obtain ⟨⟨column, S⟩, -, hp⟩ := (RingHom.ker_isPrime (evaluate B)).inf_le'.mp h
  have hle := Ideal.le_radical.trans hp
  rw [Ideal.add_eq_sup, sup_le_iff, J_le_ker_iff, J_le_ker_iff] at hle
  by_cases hS : S.Nonempty
  · by_cases hU : S = Finset.univ
    · rw [hU, Finset.compl_univ] at hle
      exact not_vanishes_empty _ hle.2
    · exact hpart column S hS hU hle
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    rw [hS] at hle
    exact not_vanishes_empty _ hle.1

/-- The right-hand side of the conjecture is not contained in the left-hand side. (The other
inclusion is Lemma 4.25 of the paper and is not needed here.) -/
theorem partitionIntersection_not_le_of_witness (B : Matrix (Fin k) (Fin k) ℂ)
    (hB : IsSingular B)
    (hpart : ∀ (column : Bool) (S : Finset (Fin k)), S.Nonempty → S ≠ Finset.univ →
      ¬ (Vanishes (orient column B) S ∧ Vanishes (orient column B) Sᶜ)) :
    ¬ partitionIntersection k ≤ (singularIdeal k).radical := by
  intro h
  apply partitionIntersection_not_le_ker B hpart
  refine h.trans ((RingHom.ker_isPrime (evaluate B)).radical_le_iff.mpr ?_)
  exact iInf_le_of_le B (iInf_le _ hB)

theorem not_conjecture_of_witness (B : Matrix (Fin k) (Fin k) ℂ) (hB : IsSingular B)
    (hpart : ∀ (column : Bool) (S : Finset (Fin k)), S.Nonempty → S ≠ Finset.univ →
      ¬ (Vanishes (orient column B) S ∧ Vanishes (orient column B) Sᶜ)) :
    ¬ Conjecture k := fun hc =>
  partitionIntersection_not_le_of_witness B hB hpart hc.ge

/-- The same conclusion for the ideal generated by the `k × k` permanents of a
`(k + 1) × (k + 1)` matrix. -/
theorem partitionIntersection_not_le_critical_of_witness
    (B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hB : ∀ r c : Fin (k + 1), (B.submatrix r.succAbove c.succAbove).permanent = 0)
    (hpart : ∀ (column : Bool) (S : Finset (Fin (k + 1))), S.Nonempty → S ≠ Finset.univ →
      ¬ (Vanishes (orient column B) S ∧ Vanishes (orient column B) Sᶜ)) :
    ¬ partitionIntersection (k + 1) ≤ (criticalIdeal k).radical := by
  intro h
  apply partitionIntersection_not_le_ker B hpart
  refine h.trans ((RingHom.ker_isPrime (evaluate B)).radical_le_iff.mpr ?_)
  rw [criticalIdeal, Ideal.span_le]
  rintro p ⟨r, c, rfl⟩
  apply RingHom.mem_ker.mpr
  rw [← hB r c]
  exact evaluate_permanent B false r.succAbove c.succAbove

end PermanentPartition
