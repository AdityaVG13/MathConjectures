import ChartJacobian.AmbientCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ComponentChartJacobian
noncomputable section
open MvPolynomial Matrix Equiv

theorem generator_vanishes_at_seed (k : ℕ) (r : Generators k) :
    eval (seed k) (generator k r) = 0 := by
  rcases r with r | (_ | (r | r))
  · change eval (seed k) (rename bVar
      ((ComponentUpperSeed.genericB.submatrix id r.succAbove).permanent)) = 0
    rw [eval_rename, ← ComponentFamilyContainment.permanent_map (eval (seed k ∘ bVar))]
    have he : ((ComponentUpperSeed.genericB.submatrix id r.succAbove).map
        (eval (seed k ∘ bVar))) = ComponentUpperSeed.B.submatrix id r.succAbove := by
      ext i j : 2
      simp [ComponentUpperSeed.genericB, Matrix.submatrix, seed, bVar]
    rw [he]
    exact ComponentUpperSeed.maximal_permanents_zero r
  · change eval (seed k) (rename wVar (genericW k).permanent) = 0
    rw [eval_rename, ← ComponentFamilyContainment.permanent_map (eval (seed k ∘ wVar))]
    have he : (genericW k).map (eval (seed k ∘ wVar)) = SparseSeed.finArrowhead k := by
      ext i j : 2
      simp [genericW, seed, wVar]
    rw [he, SparseSeed.finArrowhead, ComponentGeneralLaplace.permanent_reindex,
      SparseSeed.permanent_arrowhead]
  · simp [generator, lVar, seed]
  · simp [generator, proportionality, bVar, vVar, seed, ComponentUpperSeed.v, ComponentUpperSeed.B]
    ring

/-- The differentials of the actual chart equations are linearly independent
at this explicit seed. -/
theorem differentials_linearlyIndependent (k : ℕ) :
    LinearIndependent ℂ (fullJacobian k).row := by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  change Fintype.card (Generators k) = _
  rw [Set.finrank, ← Matrix.rank_eq_finrank_span_row, full_jacobian_rank, generator_count]

/-- The chart Jacobian maps ambient tangent vectors onto all normal values. -/
theorem differential_surjective (k : ℕ) : (fullJacobian k).mulVec.Surjective := by
  apply Matrix.mulVec_surjective_iff_rank_eq_card.mpr
  rw [full_jacobian_rank, generator_count]

#print axioms generator_vanishes_at_seed
#print axioms differentials_linearlyIndependent
#print axioms differential_surjective
end
end ComponentChartJacobian
