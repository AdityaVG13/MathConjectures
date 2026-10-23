import UniformNormalKernel
import Mathlib.Tactic

set_option autoImplicit false
namespace UniformRestrictedQuadratic

/-- Algebraic elimination of the hub coordinate from the proposed quadratic jet.
The assertion that this jet is the actual permanent's jet is a separate obligation. -/
theorem eliminate_hub (l : ℕ) (q0 S Z : ℂ)
    (h : (2*(l:ℂ)+1)*q0+(2*(l:ℂ)-3)*S=0) :
    (8*(l:ℂ)-4)*q0*S+(8*(l:ℂ)-20)*(S^2-Z) =
      UniformBlockNormal.diagonal l*Z+UniformBlockNormal.common l*S^2 := by
  unfold UniformBlockNormal.diagonal UniformBlockNormal.common
  apply (mul_left_cancel₀ (UniformBlockNormal.denominator_ne_zero l))
  have hc : (2*(l:ℂ)+1)*(-32/(2*(l:ℂ)+1)) = -32 := by
    field_simp [UniformBlockNormal.denominator_ne_zero l]
  simp only [mul_add]
  rw [← mul_assoc (2*(l:ℂ)+1) (-32/(2*(l:ℂ)+1)), hc]
  linear_combination (8*(l:ℂ)-4)*S*h

#print axioms eliminate_hub
end UniformRestrictedQuadratic
