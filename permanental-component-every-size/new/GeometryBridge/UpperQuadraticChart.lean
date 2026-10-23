import GeometryBridge.MinimalPrimeDimension
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

namespace UniformUpperQuadratic
noncomputable section
open Polynomial

def alpha {R : Type*} [CommRing R] (d h : R) : R := (d+1)*h+d-1
def beta {R : Type*} [CommRing R] (d h : R) : R :=
  (d+1)*h*(d-1)+(d+1)*h^2+d*(d-1)
def gamma {R : Type*} [CommRing R] (d h : R) : R := -d*(d+1)*h-d*(d+1)*h^2

def disc {R : Type*} [CommRing R] (d h : R) : R :=
  beta d h ^ 2 - 4 * alpha d h * gamma d h
def normPlus {R : Type*} [CommRing R] (d h : R) : R :=
  alpha d h - beta d h + gamma d h
def normMinus {R : Type*} [CommRing R] (d h : R) : R :=
  alpha d h*d^2 + beta d h*d + gamma d h
def rest {R : Type*} [CommRing R] (d h : R) : R :=
  disc d h * normPlus d h * normMinus d h
def denom {R : Type*} [CommRing R] (d h : R) : R := alpha d h * rest d h

abbrev Parameters := MvPolynomial (Fin 2) ℂ
def d : Parameters := MvPolynomial.X 0
def h : Parameters := MvPolynomial.X 1
abbrev Base := Localization.Away (denom d h)

theorem denom_ne_zero : denom d h ≠ 0 := by
  intro heq
  have he := congrArg (MvPolynomial.eval ![(2:ℂ), -35/33]) heq
  norm_num [denom, rest, disc, normPlus, normMinus, alpha, beta, gamma, d, h] at he

instance : IsDomain Base := Localization.Away.isDomain denom_ne_zero

def alphaInv : Base := algebraMap Parameters Base (rest d h) *
  IsLocalization.Away.invSelf (denom d h)

theorem alpha_mul_inv : algebraMap Parameters Base (alpha d h) * alphaInv = 1 := by
  rw [alphaInv, ← mul_assoc, ← map_mul]
  exact IsLocalization.Away.mul_invSelf (denom d h)

def b : Base := algebraMap Parameters Base (beta d h) * alphaInv
def c : Base := algebraMap Parameters Base (gamma d h) * alphaInv
def equation : Polynomial Base := C 1 * X^2 + C b * X + C c

theorem equation_monic : equation.Monic := by
  exact Polynomial.leadingCoeff_quadratic (one_ne_zero : (1:Base) ≠ 0)

theorem equation_natDegree : equation.natDegree = 2 :=
  Polynomial.natDegree_quadratic (one_ne_zero : (1:Base) ≠ 0)

abbrev Chart := AdjoinRoot equation
instance : Module.Free Base Chart := equation_monic.free_adjoinRoot
instance : Module.Finite Base Chart := equation_monic.finite_adjoinRoot
instance : Module.Flat Base Chart := inferInstance
instance : Algebra.IsIntegral Base Chart := inferInstance

theorem chart_finrank : Module.finrank Base Chart = 2 := by
  rw [(AdjoinRoot.powerBasis' equation_monic).finrank]
  exact equation_natDegree

theorem component_dimension (Q : Ideal Chart) (hQ : IsMinimalPrime Q) :
    ringKrullDim (Chart ⧸ Q) = ringKrullDim Base :=
  UniformComponentGeometry.ringKrullDim_minimalPrime_quotient (R := Base) Q hQ

theorem relation_expansion {T : Type*} [CommRing T] (d h j : T) :
    (d+1)*h*(j+d)*(j-1)+(d+1)*h*h*(j-d)+(d-1)*j*(j+d) =
      alpha d h*j^2 + beta d h*j + gamma d h := by
  simp only [alpha, beta, gamma]
  ring

def j : Chart := AdjoinRoot.root equation

theorem root_equation : j^2 + algebraMap Base Chart b*j + algebraMap Base Chart c = 0 := by
  have he := AdjoinRoot.eval₂_root equation
  change Polynomial.eval₂ (algebraMap Base Chart) j (C 1 * X^2 + C b * X + C c) = 0 at he
  simpa only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, map_one, one_mul] using he

theorem alpha_mul_b : algebraMap Parameters Base (alpha d h) * b =
    algebraMap Parameters Base (beta d h) := by
  dsimp [b]
  calc
    _ = algebraMap Parameters Base (beta d h) *
      (algebraMap Parameters Base (alpha d h) * alphaInv) := by ring
    _ = _ := by rw [alpha_mul_inv, mul_one]

theorem alpha_mul_c : algebraMap Parameters Base (alpha d h) * c =
    algebraMap Parameters Base (gamma d h) := by
  dsimp [c]
  calc
    _ = algebraMap Parameters Base (gamma d h) *
      (algebraMap Parameters Base (alpha d h) * alphaInv) := by ring
    _ = _ := by rw [alpha_mul_inv, mul_one]

/-- In a quadratic root algebra, inverting the value at t makes root minus t a unit. -/
theorem quadratic_root_shift_isUnit {T : Type*} [CommRing T]
    (a b c j t : T) (hj : a*j^2+b*j+c=0)
    (hu : IsUnit (a*t^2+b*t+c)) : IsUnit (j-t) := by
  have he : (j-t)*(a*(j+t)+b) = -(a*t^2+b*t+c) := by
    linear_combination hj
  apply isUnit_of_mul_isUnit_left (y := a*(j+t)+b)
  rw [he]
  exact hu.neg

def parameterMap : Parameters →+* Chart :=
  (algebraMap Base Chart).comp (algebraMap Parameters Base)

theorem original_root_equation :
    parameterMap (alpha d h)*j^2 + parameterMap (beta d h)*j +
      parameterMap (gamma d h) = 0 := by
  have hb := congrArg (algebraMap Base Chart) alpha_mul_b
  have hc := congrArg (algebraMap Base Chart) alpha_mul_c
  simp only [map_mul] at hb hc
  change algebraMap Base Chart (algebraMap Parameters Base (alpha d h))*j^2 +
    algebraMap Base Chart (algebraMap Parameters Base (beta d h))*j +
    algebraMap Base Chart (algebraMap Parameters Base (gamma d h)) = 0
  rw [← hb, ← hc]
  linear_combination algebraMap Base Chart (algebraMap Parameters Base (alpha d h)) * root_equation

theorem normPlus_unit : IsUnit (parameterMap (normPlus d h)) := by
  apply IsUnit.map (algebraMap Base Chart)
  apply IsLocalization.Away.isUnit_of_dvd (x := denom d h)
  use alpha d h * disc d h * normMinus d h
  simp only [denom, rest]
  ring

theorem normMinus_unit : IsUnit (parameterMap (normMinus d h)) := by
  apply IsUnit.map (algebraMap Base Chart)
  apply IsLocalization.Away.isUnit_of_dvd (x := denom d h)
  use alpha d h * disc d h * normPlus d h
  simp only [denom, rest]
  ring

theorem root_add_one_unit : IsUnit (j+1) := by
  have hu : IsUnit (parameterMap (alpha d h)*(-1)^2 +
      parameterMap (beta d h)*(-1) + parameterMap (gamma d h)) := by
    simpa [normPlus, sub_eq_add_neg] using normPlus_unit
  simpa using quadratic_root_shift_isUnit _ _ _ j (-1) original_root_equation hu

theorem root_sub_d_unit : IsUnit (j-parameterMap d) := by
  have hu : IsUnit (parameterMap (alpha d h)*(parameterMap d)^2 +
      parameterMap (beta d h)*parameterMap d + parameterMap (gamma d h)) := by
    simpa [normMinus] using normMinus_unit
  exact quadratic_root_shift_isUnit _ _ _ j (parameterMap d) original_root_equation hu

#print axioms root_add_one_unit
#print axioms root_sub_d_unit
#print axioms quadratic_root_shift_isUnit
#print axioms alpha_mul_inv
#print axioms chart_finrank
#print axioms component_dimension
end
end UniformUpperQuadratic
