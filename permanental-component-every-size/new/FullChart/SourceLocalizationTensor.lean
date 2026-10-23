import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

namespace TensorAwayPair
noncomputable section
open scoped TensorProduct
open TensorProduct
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

abbrev T (A B : Type*) [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B] := A ⊗[ℂ] B

def denominator (a : A) (b : B) : T A B := (a ⊗ₜ[ℂ] (1 : B)) * ((1 : A) ⊗ₜ[ℂ] b)
abbrev S (a : A) (b : B) := Localization.Away (denominator a b)
abbrev U (a : A) (b : B) := Localization.Away a ⊗[ℂ] Localization.Away b

def toTensor (a : A) (b : B) : T A B →ₐ[ℂ] U a b :=
  Algebra.TensorProduct.map (Algebra.algHom ℂ A (Localization.Away a))
    (Algebra.algHom ℂ B (Localization.Away b))

theorem toTensor_unit (a : A) (b : B) : IsUnit (toTensor a b (denominator a b)) := by
  unfold denominator
  rw [map_mul]
  apply IsUnit.mul
  · have h := (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a).map
      (Algebra.TensorProduct.includeLeft : Localization.Away a →ₐ[ℂ] U a b)
    simpa [toTensor, Algebra.algHom] using h
  · have h := (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away b) b).map
      (Algebra.TensorProduct.includeRight : Localization.Away b →ₐ[ℂ] U a b)
    simpa [toTensor, Algebra.algHom] using h

def forward (a : A) (b : B) : S a b →ₐ[ℂ] U a b :=
  IsLocalization.Away.liftAlgHom (denominator a b) (toTensor_unit a b)

def leftBase (a : A) (b : B) : A →ₐ[ℂ] S a b :=
  (Algebra.algHom ℂ (T A B) (S a b)).comp Algebra.TensorProduct.includeLeft

def rightBase (a : A) (b : B) : B →ₐ[ℂ] S a b :=
  (Algebra.algHom ℂ (T A B) (S a b)).comp Algebra.TensorProduct.includeRight

theorem bases_unit (a : A) (b : B) : IsUnit (leftBase a b a * rightBase a b b) := by
  change IsUnit (algebraMap (T A B) (S a b) (a ⊗ₜ[ℂ] (1:B)) *
    algebraMap (T A B) (S a b) ((1:A) ⊗ₜ[ℂ] b))
  rw [← map_mul]
  exact IsLocalization.Away.algebraMap_isUnit (S := S a b) (denominator a b)

def left (a : A) (b : B) : Localization.Away a →ₐ[ℂ] S a b :=
  IsLocalization.Away.liftAlgHom a (isUnit_of_mul_isUnit_left (bases_unit a b))

def right (a : A) (b : B) : Localization.Away b →ₐ[ℂ] S a b :=
  IsLocalization.Away.liftAlgHom b (isUnit_of_mul_isUnit_right (bases_unit a b))

def backward (a : A) (b : B) : U a b →ₐ[ℂ] S a b :=
  Algebra.TensorProduct.lift (left a b) (right a b) (fun _ _ => Commute.all _ _)

@[simp] theorem forward_base (a : A) (b : B) (x : T A B) :
    forward a b (algebraMap (T A B) (S a b) x) = toTensor a b x :=
  IsLocalization.Away.lift_eq _ (toTensor_unit a b) x

@[simp] theorem left_base (a : A) (b : B) (x : A) :
    left a b (algebraMap A (Localization.Away a) x) = leftBase a b x :=
  IsLocalization.Away.lift_eq _ (isUnit_of_mul_isUnit_left (bases_unit a b)) x

@[simp] theorem right_base (a : A) (b : B) (x : B) :
    right a b (algebraMap B (Localization.Away b) x) = rightBase a b x :=
  IsLocalization.Away.lift_eq _ (isUnit_of_mul_isUnit_right (bases_unit a b)) x

theorem backward_forward (a : A) (b : B) :
    (backward a b).comp (forward a b) = AlgHom.id ℂ (S a b) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (denominator a b))
  apply Algebra.TensorProduct.ext
  · ext x
    change backward a b (forward a b (algebraMap (T A B) (S a b) (x ⊗ₜ[ℂ] (1:B)))) =
      algebraMap (T A B) (S a b) (x ⊗ₜ[ℂ] (1:B))
    rw [forward_base]
    simp [toTensor, backward, left_base, leftBase, Algebra.algHom]
  · ext x
    change backward a b (forward a b (algebraMap (T A B) (S a b) ((1:A) ⊗ₜ[ℂ] x))) =
      algebraMap (T A B) (S a b) ((1:A) ⊗ₜ[ℂ] x)
    rw [forward_base]
    simp [toTensor, backward, right_base, rightBase, Algebra.algHom]

theorem forward_backward (a : A) (b : B) :
    (forward a b).comp (backward a b) = AlgHom.id ℂ (U a b) := by
  apply Algebra.TensorProduct.ext
  · apply IsLocalization.algHom_ext (Submonoid.powers a)
    ext x
    change forward a b (backward a b ((algebraMap A (Localization.Away a) x) ⊗ₜ[ℂ] 1)) =
      (algebraMap A (Localization.Away a) x) ⊗ₜ[ℂ] 1
    simp only [backward, Algebra.TensorProduct.lift_tmul, map_one, mul_one, left_base]
    change forward a b (algebraMap (T A B) (S a b) (x ⊗ₜ[ℂ] (1:B))) = _
    rw [forward_base]
    simp [toTensor, Algebra.algHom]
  · apply IsLocalization.algHom_ext (Submonoid.powers b)
    ext x
    change forward a b (backward a b (1 ⊗ₜ[ℂ] (algebraMap B (Localization.Away b) x))) =
      1 ⊗ₜ[ℂ] (algebraMap B (Localization.Away b) x)
    simp only [backward, Algebra.TensorProduct.lift_tmul, map_one, one_mul, right_base]
    change forward a b (algebraMap (T A B) (S a b) ((1:A) ⊗ₜ[ℂ] x)) = _
    rw [forward_base]
    simp [toTensor, Algebra.algHom]

/-- Inverting one element in each tensor factor is exactly a single principal localization. -/
def equivalence (a : A) (b : B) : S a b ≃ₐ[ℂ] U a b :=
  AlgEquiv.ofAlgHom (forward a b) (backward a b) (forward_backward a b) (backward_forward a b)

end
end TensorAwayPair

#print axioms TensorAwayPair.equivalence
