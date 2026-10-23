import MonomialUnit
namespace ExceptionalFormal
open MvPowerSeries

noncomputable def scaleAt {σ : Type*} [DecidableEq σ] (i : σ) (c : ℂ) : σ → ℂ :=
  fun j => if j = i then c else 1

theorem coeff_rescale_at_zero {σ : Type*} [DecidableEq σ]
    (f : MvPowerSeries σ ℂ) (i : σ) (c : ℂ) (n : σ →₀ ℕ)
    (hn : n i = 0) : coeff n (rescale (scaleAt i c) f) = coeff n f := by
  rw [coeff_rescale]
  have hp : n.prod (fun j k => scaleAt i c j ^ k) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    by_cases hji : j = i
    · subst j
      simp [hn]
    · simp [scaleAt, hji]
  rw [hp, one_mul]

theorem anti_invariance_zero_exponent {σ : Type*} [DecidableEq σ]
    (f : MvPowerSeries σ ℂ) (i : σ)
    (h : rescale (scaleAt i (-1)) f = -f)
    (n : σ →₀ ℕ) (hn : n i = 0) : coeff n f = 0 := by
  have he := congrArg (coeff n) h
  rw [coeff_rescale_at_zero f i (-1) n hn] at he
  simp only [map_neg] at he
  linear_combination (1/2 : ℂ) * he

theorem restriction_zero_exponent {σ : Type*} [DecidableEq σ]
    (f : MvPowerSeries σ ℂ) (i : σ)
    (h : rescale (scaleAt i 0) f = 0)
    (n : σ →₀ ℕ) (hn : n i = 0) : coeff n f = 0 := by
  have he := congrArg (coeff n) h
  rw [coeff_rescale_at_zero f i 0 n hn] at he
  simpa using he

#print axioms anti_invariance_zero_exponent
end ExceptionalFormal
