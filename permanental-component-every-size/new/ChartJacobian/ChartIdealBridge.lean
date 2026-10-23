import ChartJacobian.SeedAndRank
import FamilyContainment.ChartIdeal
import UpperSeed.LiteralUpper

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ComponentChartJacobian
noncomputable section
open MvPolynomial Matrix Equiv ComponentFamilyContainment

def blockU (k : ℕ) := (blockB k).submatrix id Fin.castSucc

theorem upperPolynomial_last (k : ℕ) : upperPolynomial k 3 = (blockU k).permanent := by
  rw [upperPolynomial_actual, blockU, ComponentLiteralUpper.first_three_is_literal_minor]

theorem upperPolynomial_cast (k : ℕ) (j : Fin 3) : upperPolynomial k j.castSucc =
    (augmented ((blockU k).submatrix id j.succAbove) (fun i => blockV k i 0)).permanent := by
  rw [upperPolynomial_actual, ← ComponentLiteralUpper.augmented_is_literal_minor]
  rfl

/-- The polynomials whose Jacobian was computed are exactly the generators of
the explicit ambient chart ideal used in the containment theorem. -/
theorem generator_range (k : ℕ) : Set.range (generator k) =
    chartGenerators (blockU k) (blockV k) (blockL k) (blockW k) := by
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    rcases r with r | (_ | (r | r))
    · change upperPolynomial k r ∈ _
      refine Fin.lastCases ?_ (fun j => ?_) r
      · rw [show Fin.last 3 = (3 : Fin 4) from rfl, upperPolynomial_last]
        exact Or.inl (Or.inl (Or.inr (by simp)))
      · rw [upperPolynomial_cast]
        exact Or.inl (Or.inr ⟨j, rfl⟩)
    · change lowerPolynomial k ∈ _
      rw [lowerPolynomial_actual]
      exact Or.inl (Or.inl (Or.inr (by simp)))
    · exact Or.inl (Or.inl (Or.inl ⟨r, rfl⟩))
    · change proportionality k r ∈ _
      rw [proportionality_actual]
      exact Or.inr ⟨r, rfl⟩
  · intro hx
    rcases hx with ((hL | hWU) | hB) | hP
    · obtain ⟨r, rfl⟩ := hL
      exact ⟨Sum.inr (Sum.inr (Sum.inl r)), rfl⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hWU
      rcases hWU with rfl | rfl
      · exact ⟨Sum.inr (Sum.inl ()), lowerPolynomial_actual k⟩
      · exact ⟨Sum.inl 3, upperPolynomial_last k⟩
    · obtain ⟨j, rfl⟩ := hB
      exact ⟨Sum.inl j.castSucc, upperPolynomial_cast k j⟩
    · obtain ⟨r, rfl⟩ := hP
      exact ⟨Sum.inr (Sum.inr (Sum.inr r)), proportionality_actual k r⟩

theorem generator_ideal (k : ℕ) : Ideal.span (Set.range (generator k)) =
    chartIdeal (blockU k) (blockV k) (blockL k) (blockW k) := by
  rw [generator_range]
  rfl

#print axioms generator_ideal
end
end ComponentChartJacobian
