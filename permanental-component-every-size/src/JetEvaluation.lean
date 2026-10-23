import ConcreteLocalSetup
import Mathlib.Algebra.MvPolynomial.PDeriv
namespace ConcreteLocalGeometry
open MvPolynomial
noncomputable def firstDerivative (i : Fin 16) (f : P) : ℂ := evalOrigin (pderiv i f)
noncomputable def secondDerivative (i j : Fin 16) (f : P) : ℂ :=
  evalOrigin (pderiv i (pderiv j f))
@[simp] theorem first_add (i : Fin 16) (f g : P) : firstDerivative i (f+g) = firstDerivative i f + firstDerivative i g := by simp [firstDerivative]
@[simp] theorem first_sub (i : Fin 16) (f g : P) : firstDerivative i (f-g) = firstDerivative i f - firstDerivative i g := by simp [firstDerivative]
@[simp] theorem first_neg (i : Fin 16) (f : P) : firstDerivative i (-f) = -firstDerivative i f := by simp [firstDerivative]
@[simp] theorem first_mul (i : Fin 16) (f g : P) : firstDerivative i (f*g) = firstDerivative i f * evalOrigin g + evalOrigin f * firstDerivative i g := by simp [firstDerivative]; ring
@[simp] theorem first_C (i : Fin 16) (c : ℂ) : firstDerivative i (C c) = 0 := by simp [firstDerivative]
@[simp] theorem first_one (i : Fin 16) : firstDerivative i 1 = 0 := by simp [firstDerivative]
@[simp] theorem first_zero (i : Fin 16) : firstDerivative i 0 = 0 := by simp [firstDerivative]
@[simp] theorem first_X (i j : Fin 16) : firstDerivative i (X j) = if j=i then 1 else 0 := by simp [firstDerivative,Pi.single_apply]
@[simp] theorem second_add (i j : Fin 16) (f g : P) : secondDerivative i j (f+g) = secondDerivative i j f + secondDerivative i j g := by simp [secondDerivative]
@[simp] theorem second_sub (i j : Fin 16) (f g : P) : secondDerivative i j (f-g) = secondDerivative i j f - secondDerivative i j g := by simp [secondDerivative]
@[simp] theorem second_neg (i j : Fin 16) (f : P) : secondDerivative i j (-f) = -secondDerivative i j f := by simp [secondDerivative]
@[simp] theorem second_mul (i j : Fin 16) (f g : P) : secondDerivative i j (f*g) = secondDerivative i j f * evalOrigin g + firstDerivative j f * firstDerivative i g + firstDerivative i f * firstDerivative j g + evalOrigin f * secondDerivative i j g := by simp [secondDerivative,firstDerivative]; ring
@[simp] theorem second_C (i j : Fin 16) (c : ℂ) : secondDerivative i j (C c) = 0 := by simp [secondDerivative]
@[simp] theorem second_one (i j : Fin 16) : secondDerivative i j 1 = 0 := by simp [secondDerivative]
@[simp] theorem second_zero (i j : Fin 16) : secondDerivative i j 0 = 0 := by simp [secondDerivative]
@[simp] theorem second_X (i j k : Fin 16) : secondDerivative i j (X k) = 0 := by
  simp only [secondDerivative,pderiv_X,Pi.single_apply]
  split <;> simp
end ConcreteLocalGeometry
