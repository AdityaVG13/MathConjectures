/- Adapted from mathlib's determinant block proof, removing determinant signs.
This standard permanent identity is infrastructure, not an originality claim. -/
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
namespace ComponentBlockPermanent
open Matrix Equiv Equiv.Perm Finset
variable {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [CommRing R]
set_option backward.isDefEq.respectTransparency false in
theorem permanent_fromBlocks_zero_lower (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    (Matrix.fromBlocks A B 0 D).permanent = A.permanent * D.permanent := by
  classical
    simp_rw [Matrix.permanent]
    convert
      Eq.symm <|
        sum_subset (M := R) (subset_univ ((sumCongrHom m n).range : Set (Perm (m ⊕ n))).toFinset) ?_
    · simp_rw [sum_mul_sum, ← sum_product', univ_product_univ]
      refine sum_nbij (fun σ ↦ σ.fst.sumCongr σ.snd) ?_ ?_ ?_ ?_
      · intro σ₁₂ _
        simp
      · intro σ₁ _ σ₂ _
        dsimp only
        intro h
        have h2 : ∀ x, Perm.sumCongr σ₁.fst σ₁.snd x = Perm.sumCongr σ₂.fst σ₂.snd x :=
          DFunLike.congr_fun h
        simp only [Sum.map_inr, Sum.map_inl, Perm.sumCongr_apply, Sum.forall, Sum.inl.injEq,
          Sum.inr.injEq] at h2
        ext x
        · exact h2.left x
        · exact h2.right x
      · intro σ hσ
        rw [mem_coe, Set.mem_toFinset] at hσ
        obtain ⟨σ₁₂, hσ₁₂⟩ := hσ
        use σ₁₂
        rw [← hσ₁₂]
        simp
      · simp only [forall_prop_of_true, Prod.forall, mem_univ]
        intro σ₁ σ₂
        rw [Fintype.prod_sum_type]
        simp_rw [Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl, fromBlocks_apply₁₁,
          fromBlocks_apply₂₂]
    · rintro σ - hσn
      have h1 : ¬∀ x, ∃ y, Sum.inl y = σ (Sum.inl x) := by
        rw [Set.mem_toFinset] at hσn
        simpa only [Set.MapsTo, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] using
          mt mem_sumCongrHom_range_of_perm_mapsTo_inl hσn
      obtain ⟨a, ha⟩ := not_forall.mp h1
      rcases hx : σ (Sum.inl a) with a2 | b
      · have hn := (not_exists.mp ha) a2
        exact absurd hx.symm hn
      · rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inl a))]
        rw [hx, fromBlocks_apply₂₁, Matrix.zero_apply]


#print axioms permanent_fromBlocks_zero_lower
end ComponentBlockPermanent
