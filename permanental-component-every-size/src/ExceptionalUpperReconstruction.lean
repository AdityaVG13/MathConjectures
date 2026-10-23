import ExceptionalUpperRoot
import ExceptionalIntrinsicElimination

set_option autoImplicit false
namespace ExceptionalUpperFormal

noncomputable def denUnit : Sˣ := denominator_unit.unit
theorem denUnit_value : (denUnit : S) = 2*ExceptionalCriticalFamily.denominator d root :=
  denominator_unit.unit_spec
noncomputable def e : S := ExceptionalUpper.eOut d h root p c0 c1 c2 * (↑(denUnit⁻¹) : S)
noncomputable def f : S := ExceptionalUpper.fOut d h root p c0 c1 c2 * (↑(denUnit⁻¹) : S)
noncomputable def i : S := ExceptionalUpper.iOut d h root p c0 c1 c2 * (↑(denUnit⁻¹) : S)

theorem clear_e : (denUnit : S)*e = ExceptionalUpper.eOut d h root p c0 c1 c2 := by
  rw [e, mul_left_comm, denUnit.mul_inv, mul_one]
theorem clear_f : (denUnit : S)*f = ExceptionalUpper.fOut d h root p c0 c1 c2 := by
  rw [f, mul_left_comm, denUnit.mul_inv, mul_one]
theorem clear_i : (denUnit : S)*i = ExceptionalUpper.iOut d h root p c0 c1 c2 := by
  rw [i, mul_left_comm, denUnit.mul_inv, mul_one]

theorem reconstructed_C1 : ExceptionalIntrinsic.C1 d h root e f i = c1 := by
  apply denUnit.isUnit.mul_left_cancel
  calc
    (denUnit : S)*ExceptionalIntrinsic.C1 d h root e f i =
      (d+1)*((denUnit:S)*i)+(root+1)*((denUnit:S)*f)+(d+root)*(denUnit:S) := by
        unfold ExceptionalIntrinsic.C1; ring
    _ = c1*(denUnit:S) := by
      rw [clear_i,clear_f,denUnit_value]
      exact ExceptionalUpper.c1_identity d h root p c0 c1 c2
    _ = (denUnit:S)*c1 := mul_comm _ _

theorem reconstructed_C2 : ExceptionalIntrinsic.C2 d h root e f i = c2 := by
  apply denUnit.isUnit.mul_left_cancel
  calc
    (denUnit:S)*ExceptionalIntrinsic.C2 d h root e f i =
      (root+1)*((denUnit:S)*e)+((d+1)*h+d+root)*(denUnit:S) := by
        unfold ExceptionalIntrinsic.C2; ring
    _ = c2*(denUnit:S) := by
      rw [clear_e,denUnit_value]
      exact ExceptionalUpper.c2_identity d h root p c0 c1 c2
    _ = (denUnit:S)*c2 := mul_comm _ _

theorem clear_P : (denUnit:S)^2*ExceptionalIntrinsic.P d h root e f i =
    ExceptionalUpper.clearedP d h root p c0 c1 c2 := by
  calc
    _ = ((denUnit:S)*e)*((denUnit:S)*i)+((denUnit:S)*e)*(denUnit:S)+
      ((denUnit:S)*f)*h*(denUnit:S)+((denUnit:S)*f)*(denUnit:S)+
      h*(denUnit:S)^2+((denUnit:S)*i)*(denUnit:S) := by unfold ExceptionalIntrinsic.P; ring
    _ = _ := by rw [clear_e,clear_f,clear_i,denUnit_value]; rfl

theorem clear_C0 : (denUnit:S)^2*ExceptionalIntrinsic.C0 d h root e f i =
    ExceptionalUpper.clearedC0 d h root p c0 c1 c2 := by
  calc
    _ = d*h*(denUnit:S)^2+d*((denUnit:S)*i)*(denUnit:S)+
      ((denUnit:S)*e)*((denUnit:S)*i)+((denUnit:S)*e)*root*(denUnit:S)+
      ((denUnit:S)*f)*h*(denUnit:S)+((denUnit:S)*f)*root*(denUnit:S) := by
        unfold ExceptionalIntrinsic.C0; ring
    _ = _ := by rw [clear_e,clear_f,clear_i,denUnit_value]; rfl

theorem reconstructed_P : ExceptionalIntrinsic.P d h root e f i = p := by
  apply (denUnit.isUnit.pow 2).mul_left_cancel
  rw [clear_P]
  have he := ExceptionalUpper.p_identity d h root p c0 c1 c2
  rw [root_equation,mul_zero] at he
  rw [denUnit_value,mul_comm]
  exact sub_eq_zero.mp he

theorem reconstructed_C0 : ExceptionalIntrinsic.C0 d h root e f i = c0 := by
  apply (denUnit.isUnit.pow 2).mul_left_cancel
  rw [clear_C0]
  have he := ExceptionalUpper.c0_identity d h root p c0 c1 c2
  rw [root_equation,mul_zero] at he
  rw [denUnit_value,mul_comm]
  exact sub_eq_zero.mp he

/-- Actual all-orders reconstruction with four independent prescribed constraint
series. A two-sided substitution equivalence is a separate remaining obligation. -/
theorem reconstruction :
    ExceptionalIntrinsic.P d h root e f i = p ∧
    ExceptionalIntrinsic.C0 d h root e f i = c0 ∧
    ExceptionalIntrinsic.C1 d h root e f i = c1 ∧
    ExceptionalIntrinsic.C2 d h root e f i = c2 :=
  ⟨reconstructed_P,reconstructed_C0,reconstructed_C1,reconstructed_C2⟩

#print axioms reconstruction
end ExceptionalUpperFormal
