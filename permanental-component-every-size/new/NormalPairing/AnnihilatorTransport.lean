import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
namespace ComponentAnnihilatorTransport
open Matrix
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem transport (P : Matrix ι ι ℂ) (hp : IsUnit P.det)
    (L : Matrix ι κ ℂ) (z lam : ι → ℂ) (k : κ → ℂ)
    (h : ∀ i c, (P.transpose * L) i c = z i * k c)
    (hz : dotProduct lam z = 0) :
    ∃ q : ι → ℂ, (∀ i c, L i c = q i * k c) ∧ dotProduct (P.mulVec lam) q = 0 := by
  have ht : IsUnit P.transpose.det := by simpa using hp
  let q := P.transpose⁻¹.mulVec z
  have hq : P.transpose.mulVec q = z := by
    dsimp only [q]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ht, Matrix.one_mulVec]
  refine ⟨q, ?_, ?_⟩
  · intro i c
    have hc : P.transpose.mulVec (fun j => L j c) = k c • z := by
      ext j
      change (P.transpose * L) j c = k c * z j
      rw [h]
      ring
    have hi : (fun j => L j c) = k c • q := by
      calc
        _ = P.transpose⁻¹.mulVec (P.transpose.mulVec (fun j => L j c)) := by
          rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ht, Matrix.one_mulVec]
        _ = P.transpose⁻¹.mulVec (k c • z) := by rw [hc]
        _ = k c • q := Matrix.mulVec_smul _ _ _
    have hi' := congrFun hi i
    simpa [mul_comm] using hi'
  · calc
      dotProduct (P.mulVec lam) q = dotProduct lam (P.transpose.mulVec q) := by
        simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply,
          Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = dotProduct lam z := by rw [hq]
      _ = 0 := hz

#print axioms transport
end ComponentAnnihilatorTransport
