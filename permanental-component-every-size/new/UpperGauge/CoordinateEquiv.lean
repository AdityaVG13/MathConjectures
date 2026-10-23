import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace UniformUpperGauge
noncomputable section
open MvPolynomial
abbrev Index := Fin 3 × Fin 4
abbrev Pivot := Fin 4 ⊕ Fin 2
abbrev P := MvPolynomial Index ℂ

def pivot : Pivot → Index
  | Sum.inl j => (0,j)
  | Sum.inr i => (i.succ,0)
def delta : P := ∏ p : Pivot, X (pivot p)
abbrev A := Localization.Away delta

def matrix (i : Fin 3) (j : Fin 4) : A := algebraMap P A (X (i,j))
theorem pivot_isUnit (p : Pivot) : IsUnit (matrix (pivot p).1 (pivot p).2) := by
  apply IsLocalization.Away.isUnit_of_dvd delta
  exact Finset.dvd_prod_of_mem (fun p : Pivot => (X (pivot p) : P)) (Finset.mem_univ p)
def units (p : Pivot) : Aˣ := (pivot_isUnit p).unit
theorem units_value (p : Pivot) : (units p : A) = matrix (pivot p).1 (pivot p).2 :=
  (pivot_isUnit p).unit_spec

def gamma (j : Fin 4) : Aˣ := units (Sum.inl j)
def rho (i : Fin 3) : Aˣ := Fin.cases 1 (fun r => units (Sum.inr r) * (gamma 0)⁻¹) i
def scale (i : Fin 3) (j : Fin 4) : Aˣ := rho i * gamma j

@[reducible] def IsPivot (ij : Index) : Prop := ij.1 = 0 ∨ ij.2 = 0

def forwardImage (ij : Index) : A := if IsPivot ij then matrix ij.1 ij.2
  else ↑(scale ij.1 ij.2)⁻¹ * matrix ij.1 ij.2

def inverseImage (ij : Index) : A := if IsPivot ij then matrix ij.1 ij.2
  else ↑(scale ij.1 ij.2) * matrix ij.1 ij.2

@[simp] theorem forwardImage_pivot (p : Pivot) : forwardImage (pivot p) = matrix (pivot p).1 (pivot p).2 := by
  cases p <;> simp [forwardImage,IsPivot,pivot]
@[simp] theorem inverseImage_pivot (p : Pivot) : inverseImage (pivot p) = matrix (pivot p).1 (pivot p).2 := by
  cases p <;> simp [inverseImage,IsPivot,pivot]

def forwardPoly : P →+* A := eval₂Hom ((algebraMap P A).comp C) forwardImage
def inversePoly : P →+* A := eval₂Hom ((algebraMap P A).comp C) inverseImage

theorem forwardPoly_delta : forwardPoly delta = algebraMap P A delta := by
  simp [delta, forwardPoly, matrix]
theorem inversePoly_delta : inversePoly delta = algebraMap P A delta := by
  simp [delta, inversePoly, matrix]

def forwardMap : A →+* A := IsLocalization.Away.lift delta
  (show IsUnit (forwardPoly delta) by rw [forwardPoly_delta]; exact IsLocalization.Away.algebraMap_isUnit delta)
def inverseMap : A →+* A := IsLocalization.Away.lift delta
  (show IsUnit (inversePoly delta) by rw [inversePoly_delta]; exact IsLocalization.Away.algebraMap_isUnit delta)

@[simp] theorem forwardMap_matrix (i : Fin 3) (j : Fin 4) : forwardMap (matrix i j) = forwardImage (i,j) := by
  simp [forwardMap,matrix,forwardPoly]
@[simp] theorem inverseMap_matrix (i : Fin 3) (j : Fin 4) : inverseMap (matrix i j) = inverseImage (i,j) := by
  simp [inverseMap,matrix,inversePoly]

theorem forwardMap_units (p : Pivot) : Units.map forwardMap.toMonoidHom (units p) = units p := by
  apply Units.ext
  change forwardMap (units p : A) = (units p : A)
  rw [units_value, forwardMap_matrix]
  exact forwardImage_pivot p

theorem inverseMap_units (p : Pivot) : Units.map inverseMap.toMonoidHom (units p) = units p := by
  apply Units.ext
  change inverseMap (units p : A) = (units p : A)
  rw [units_value, inverseMap_matrix]
  exact inverseImage_pivot p

theorem map_scale (f : A →+* A) (h : ∀ p, Units.map f.toMonoidHom (units p) = units p)
    (i : Fin 3) (j : Fin 4) : Units.map f.toMonoidHom (scale i j) = scale i j := by
  refine Fin.cases ?_ (fun r => ?_) i <;> simp only [scale, rho, gamma, Fin.cases_zero, Fin.cases_succ, map_mul, map_inv, map_one]; all_goals simp only [h]

theorem inverse_forward_matrix (i : Fin 3) (j : Fin 4) :
    inverseMap (forwardMap (matrix i j)) = matrix i j := by
  have hs := congrArg (fun u : Aˣ => (u : A)) (map_scale inverseMap inverseMap_units i j)
  have hsi := congrArg (fun u : Aˣ => (u : A)) (show Units.map inverseMap.toMonoidHom
      (scale i j)⁻¹ = (scale i j)⁻¹ by rw [map_inv,map_scale inverseMap inverseMap_units])
  change inverseMap (↑(scale i j)⁻¹) = ↑(scale i j)⁻¹ at hsi
  rw [forwardMap_matrix]
  by_cases hp : IsPivot (i,j)
  · simp [forwardImage,inverseImage,hp]
  · simp [forwardImage,inverseImage,hp,hsi,←mul_assoc]

theorem forward_inverse_matrix (i : Fin 3) (j : Fin 4) :
    forwardMap (inverseMap (matrix i j)) = matrix i j := by
  have hs := congrArg (fun u : Aˣ => (u : A)) (map_scale forwardMap forwardMap_units i j)
  change forwardMap (scale i j : A) = (scale i j : A) at hs
  rw [inverseMap_matrix]
  by_cases hp : IsPivot (i,j)
  · simp [forwardImage,inverseImage,hp]
  · simp [forwardImage,inverseImage,hp,hs,←mul_assoc]

theorem inverse_comp_forward : inverseMap.comp forwardMap = RingHom.id A := by
  apply IsLocalization.ringHom_ext (Submonoid.powers delta)
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [forwardMap,inverseMap,forwardPoly,inversePoly]
  · intro ij
    exact inverse_forward_matrix ij.1 ij.2

theorem forward_comp_inverse : forwardMap.comp inverseMap = RingHom.id A := by
  apply IsLocalization.ringHom_ext (Submonoid.powers delta)
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [forwardMap,inverseMap,forwardPoly,inversePoly]
  · intro ij
    exact forward_inverse_matrix ij.1 ij.2

/-- Actual coordinate-ring automorphism on the six-pivot open set.
The six pivot coordinates are retained; the other six coordinates are normalized. -/
def coordinateRingEquiv : A ≃+* A :=
  { forwardMap with
    invFun := inverseMap
    left_inv := fun x => RingHom.congr_fun inverse_comp_forward x
    right_inv := fun x => RingHom.congr_fun forward_comp_inverse x }

#print axioms coordinateRingEquiv
end
end UniformUpperGauge
