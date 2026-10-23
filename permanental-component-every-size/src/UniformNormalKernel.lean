import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
namespace UniformBlockNormal
noncomputable def diagonal (l : ℕ) : ℂ := -4*(2*(l:ℂ)-5)
noncomputable def common (l : ℕ) : ℂ := -32/(2*(l:ℂ)+1)

theorem denominator_ne_zero (l : ℕ) : 2*(l:ℂ)+1 ≠ 0 := by
  exact_mod_cast (show 2*(l:ℤ)+1 ≠ 0 by omega)

theorem diagonal_ne_zero (l : ℕ) : diagonal l ≠ 0 := by
  unfold diagonal
  apply mul_ne_zero (by norm_num)
  exact_mod_cast (show 2*(l:ℤ)-5 ≠ 0 by omega)

theorem eigenvalue_identity (l : ℕ) :
    diagonal l+(l:ℂ)*common l = -4*(4*(l:ℂ)^2-5)/(2*(l:ℂ)+1) := by
  unfold diagonal common
  field_simp [denominator_ne_zero]
  ring

theorem eigenvalue_ne_zero (l : ℕ) : diagonal l+(l:ℂ)*common l ≠ 0 := by
  rw [eigenvalue_identity]
  apply div_ne_zero _ (denominator_ne_zero l)
  apply mul_ne_zero (by norm_num)
  have hi : 4*(l:ℤ)^2-5 ≠ 0 := by omega
  exact_mod_cast hi

/-- Exact nonsingularity of the proposed restricted normal matrix D I+C J
at every size. This does not assert its identification with an ambient Hessian. -/
theorem kernel_zero (l : ℕ) (v : Fin l → ℂ)
    (h : ∀ i, diagonal l*v i+common l*(∑ j, v j)=0) : v=0 := by
  have hs : (diagonal l+(l:ℂ)*common l)*(∑ j, v j)=0 := by
    calc
      _ = ∑ i : Fin l, (diagonal l*v i+common l*(∑ j, v j)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ = 0 := Finset.sum_eq_zero (fun i _ => h i)
  have hz : (∑ j, v j)=0 := (mul_eq_zero.mp hs).resolve_left (eigenvalue_ne_zero l)
  funext i
  have hi := h i
  rw [hz,mul_zero,add_zero] at hi
  exact (mul_eq_zero.mp hi).resolve_left (diagonal_ne_zero l)

#print axioms kernel_zero
end UniformBlockNormal
