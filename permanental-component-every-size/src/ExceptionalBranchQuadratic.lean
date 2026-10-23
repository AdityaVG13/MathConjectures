import ExceptionalCriticalFamily
import MonomialUnit

set_option autoImplicit false
namespace ExceptionalBranch
variable {R : Type*} [CommRing R]

def alpha (d h : R) : R := (d+1)*h+d-1
def beta (d h : R) : R := (d+1)*h*(d-1)+(d+1)*h*h+d*(d-1)
def gamma (d h : R) : R := -d*(d+1)*h*(1+h)
def discriminant (d h : R) : R := beta d h ^ 2 - 4 * alpha d h * gamma d h

theorem relation_quadratic (d h j : R) :
    ExceptionalCriticalFamily.relation d h j = alpha d h*j^2+beta d h*j+gamma d h := by
  simp only [ExceptionalCriticalFamily.relation, alpha, beta, gamma]
  ring

theorem complete_square (d h j : R) :
    (2*alpha d h*j+beta d h)^2 - discriminant d h =
      4*alpha d h*ExceptionalCriticalFamily.relation d h j := by
  rw [relation_quadratic]
  unfold discriminant
  ring

theorem difference_factor (d h j k : R) :
    ExceptionalCriticalFamily.relation d h j - ExceptionalCriticalFamily.relation d h k =
      (j-k)*(alpha d h*(j+k)+beta d h) := by
  rw [relation_quadratic, relation_quadratic]
  ring

abbrev Series := MvPowerSeries (Fin 3) ℂ
noncomputable def d : Series := MvPowerSeries.X 0
noncomputable def h : Series := -1 + MvPowerSeries.X 1

@[simp] theorem cc_d : MvPowerSeries.constantCoeff d = 0 := by simp [d]
@[simp] theorem cc_h : MvPowerSeries.constantCoeff h = -1 := by simp [h]
@[simp] theorem cc_alpha : MvPowerSeries.constantCoeff (alpha d h) = -2 := by
  norm_num [alpha]
@[simp] theorem cc_beta : MvPowerSeries.constantCoeff (beta d h) = 2 := by
  norm_num [beta]
@[simp] theorem cc_gamma : MvPowerSeries.constantCoeff (gamma d h) = 0 := by
  norm_num [gamma]
@[simp] theorem cc_discriminant : MvPowerSeries.constantCoeff (discriminant d h) = 4 := by
  norm_num [discriminant]

theorem alpha_unit : IsUnit (alpha d h) := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, cc_alpha, isUnit_iff_ne_zero]
  norm_num

/-- Uniqueness of the actual critical-branch solution with constant j=1.
No general implicit-function theorem is assumed. -/
theorem branch_unique (j k : Series)
    (hj : MvPowerSeries.constantCoeff j = 1) (hk : MvPowerSeries.constantCoeff k = 1)
    (hrj : ExceptionalCriticalFamily.relation d h j = 0)
    (hrk : ExceptionalCriticalFamily.relation d h k = 0) : j = k := by
  have hu : IsUnit (alpha d h*(j+k)+beta d h) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    norm_num [hj,hk]
  have he := difference_factor d h j k
  rw [hrj,hrk,sub_self] at he
  have hz : j-k = 0 := hu.mul_right_cancel (by simpa using he.symm)
  exact sub_eq_zero.mp hz

#print axioms complete_square
#print axioms branch_unique
end ExceptionalBranch
