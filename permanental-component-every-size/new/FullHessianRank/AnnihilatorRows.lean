import NormalPairing.UpperPairing
import NormalPairing.AnnihilatorTransport

set_option autoImplicit false
namespace ComponentFullHessianRank
open Matrix ComponentUpperSeed
noncomputable section

theorem row_of_two_coordinates (row : Fin 3 → ℂ)
    (h : ∀ i : Fin 2, ∑ c : Fin 3, T c i.succ * row c = 0) :
    row = (row 0 / 1034) • ComponentUpperSeed.k := by
  apply ComponentUpperPairing.annihilator_complement
  intro w hw
  have h0 := h 0
  have h1 := h 1
  norm_num [Fin.sum_univ_succ] at h0 h1
  simp only [dotProduct, Matrix.mulVec]
  norm_num [Fin.sum_univ_succ, hw]
  linear_combination w 1 * h0 + w 2 * h1

theorem annihilator_rows_fin (n : ℕ) (lam : Fin (n+1) → ℂ) (hlam : lam 0 = 1)
    (L : Matrix (Fin (n+1)) (Fin 3) ℂ)
    (hw : ∀ j : Fin n, ∀ i : Fin 2, ∑ c : Fin 3, T c i.succ * L j.succ c = 0)
    (hc : ∀ c, ∑ j, lam j * L j c = 0) :
    ∃ z : Fin (n+1) → ℂ,
      (∀ j c, L j c = z j * ComponentUpperSeed.k c) ∧ dotProduct lam z = 0 := by
  let zs : Fin n → ℂ := fun j => L j.succ 0 / 1034
  have hs (j : Fin n) : L j.succ = zs j • ComponentUpperSeed.k :=
    row_of_two_coordinates _ (hw j)
  let z : Fin (n+1) → ℂ := Fin.cases (-(∑ a : Fin n, lam a.succ * zs a)) zs
  refine ⟨z, ?_, ?_⟩
  · intro j c
    refine Fin.cases ?_ (fun j => ?_) j
    · have hi := hc c
      simp only [Fin.sum_univ_succ, hlam, one_mul] at hi
      have he : (∑ j : Fin n, lam j.succ * L j.succ c) =
          (∑ j : Fin n, lam j.succ * zs j) * ComponentUpperSeed.k c := by
        simp only [hs, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [he] at hi
      change L 0 c = (-(∑ a : Fin n, lam a.succ * zs a)) * ComponentUpperSeed.k c
      linear_combination hi
    · exact congrFun (hs j) c
  · simp [dotProduct, z, Fin.sum_univ_succ, hlam]

/-- Complete algebraic passage from transformed annihilator coordinates to
rank-one lower-left matrices, with the genuine cofactor-weight constraint. -/
theorem annihilator_rank_one (n : ℕ) (P : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hp : IsUnit P.det) (lam : Fin (n+1) → ℂ) (hlam : lam 0 = 1)
    (L : Matrix (Fin (n+1)) (Fin 3) ℂ)
    (hw : ∀ j : Fin n, ∀ i : Fin 2,
      ∑ c : Fin 3, T c i.succ * (P.transpose * L) j.succ c = 0)
    (hc : ∀ c, ∑ j, lam j * (P.transpose * L) j c = 0) :
    ∃ q : Fin (n+1) → ℂ,
      (∀ a c, L a c = q a * ComponentUpperSeed.k c) ∧ dotProduct (P.mulVec lam) q = 0 := by
  obtain ⟨z, hz, hz0⟩ := annihilator_rows_fin n lam hlam (P.transpose * L) hw hc
  exact ComponentAnnihilatorTransport.transport P hp L z lam ComponentUpperSeed.k hz hz0

#print axioms annihilator_rank_one
end
end ComponentFullHessianRank
