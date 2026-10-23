import MonomialJacobian
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

namespace ExceptionalFormal
open MvPowerSeries

/-- Coefficients in the downset of w vanish. Downset closure is essential:
vanishing of only one coefficient would not in general define an ideal. -/
noncomputable def downsetZero (w : Fin 4 →₀ ℕ) : Ideal Series where
  carrier := {f | ∀ n, n ≤ w → coeff n f = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg n hn
    simp [map_add, hf n hn, hg n hn]
  smul_mem' := by
    intro c f hf n hn
    change coeff n (c * f) = 0
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    have he : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
    have hle : p.2 ≤ n := by rw [← he]; exact le_add_left le_rfl
    rw [hf p.2 (hle.trans hn), mul_zero]

noncomputable def nilExponent : Fin 4 →₀ ℕ :=
  Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1
noncomputable def nilWitness : Series := X 0 * X 1 * X 2
noncomputable def residualExponent : Fin 4 → (Fin 4 →₀ ℕ) :=
  ![Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1 + Finsupp.single 3 1,
    Finsupp.single 0 2 + Finsupp.single 2 1 + Finsupp.single 3 1,
    Finsupp.single 0 2 + Finsupp.single 1 1 + Finsupp.single 3 1,
    Finsupp.single 0 2 + Finsupp.single 1 1 + Finsupp.single 2 1]

theorem residualGenerator_monomial (i : Fin 4) :
    residualGenerator i = monomial (residualExponent i) 1 := by
  fin_cases i <;> dsimp [residualGenerator, residualExponent]
  all_goals try rw [X_pow_eq]
  all_goals simp only [X_def, monomial_mul_monomial, one_mul]

theorem residual_not_le_nil (i : Fin 4) : ¬residualExponent i ≤ nilExponent := by
  intro h
  fin_cases i
  · have := h 3; norm_num [residualExponent, nilExponent] at this
  · have := h 0; norm_num [residualExponent, nilExponent] at this
  · have := h 0; norm_num [residualExponent, nilExponent] at this
  · have := h 0; norm_num [residualExponent, nilExponent] at this

theorem residualIdeal_le_downset : residualIdeal ≤ downsetZero nilExponent := by
  rw [residualIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩ n hn
  rw [residualGenerator_monomial, coeff_monomial]
  apply ite_eq_right
  intro he
  apply residual_not_le_nil i
  simpa [he] using hn

theorem nilWitness_not_mem : nilWitness ∉ residualIdeal := by
  intro hm
  have he := residualIdeal_le_downset hm nilExponent le_rfl
  have hm : nilWitness = monomial nilExponent 1 := by
    simp only [nilWitness, nilExponent, X_def, monomial_mul_monomial, one_mul]
  rw [hm, coeff_monomial_same] at he
  exact one_ne_zero he

theorem nilWitness_sq_mem : nilWitness ^ 2 ∈ residualIdeal := by
  have hm : residualGenerator 3 ∈ residualIdeal := Ideal.subset_span (Set.mem_range_self 3)
  have he : nilWitness ^ 2 = (X 1 * X 2) * residualGenerator 3 := by
    simp [nilWitness, residualGenerator]
    ring
  rw [he]
  exact residualIdeal.mul_mem_left _ hm

theorem residualIdeal_not_radical : ¬residualIdeal.IsRadical := by
  intro hr
  exact nilWitness_not_mem ((residualIdeal.isRadical_iff_pow_one_lt 2 (by norm_num)).mp hr
    nilWitness nilWitness_sq_mem)

theorem residualQuotient_not_reduced : ¬IsReduced (Series ⧸ residualIdeal) := by
  rw [← Ideal.isRadical_iff_quotient_reduced]
  exact residualIdeal_not_radical

#print axioms residualIdeal_not_radical
#print axioms residualQuotient_not_reduced
#print axioms nilWitness_not_mem
#print axioms nilWitness_sq_mem
end ExceptionalFormal
