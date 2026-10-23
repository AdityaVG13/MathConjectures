import BChartLocalBaseChange
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

set_option autoImplicit false
namespace BChartTransport
open PermanentGauge.Coordinates

/-- Actual residue evaluation on the chosen family local ring. -/
noncomputable def residue (s : ℂ) : LocalAt s →+* ℂ :=
  IsLocalization.lift (S := LocalAt s) (g := pointMap s) (fun y : (pointIdeal s).primeCompl => by
    apply isUnit_iff_ne_zero.mpr
    intro hy
    exact y.property (RingHom.mem_ker.mpr hy))

theorem residue_toMap (s : ℂ) (x : A) :
    residue s (algebraMap A (LocalAt s) x) = pointMap s x := by
  simp [residue]

theorem residue_polynomial (s : ℂ) (f : P25) :
    residue s (toFamilyLocal s f) = pointPoly s f := by
  simp [toFamilyLocal, residue_toMap, pointMap]

theorem residue_surjective (s : ℂ) : Function.Surjective (residue s) := by
  intro c
  refine ⟨toFamilyLocal s (MvPolynomial.C c), ?_⟩
  simp [residue_polynomial, pointPoly]

theorem unit_of_residue_ne_zero (s : ℂ) (x : LocalAt s)
    (hx : residue s x ≠ 0) : IsUnit x := by
  apply IsLocalRing.notMem_maximalIdeal.mp
  rw [← IsLocalRing.ker_eq_maximalIdeal (residue s) (residue_surjective s)]
  exact hx

/-- Lift a concrete open-ring map once its actual residue compatibility is
proved. This helper does not assume an inverse or a desired ideal equality. -/
noncomputable def extendAtPoint (s : ℂ) (g : A →+* LocalAt s)
    (hg : (residue s).comp g = pointMap s) : LocalAt s →+* LocalAt s :=
  IsLocalization.lift (S := LocalAt s) (g := g) (fun y : (pointIdeal s).primeCompl => by
    apply unit_of_residue_ne_zero s
    have he := RingHom.congr_fun hg y.val
    change residue s (g y.val) = pointMap s y.val at he
    rw [he]
    intro hy
    exact y.property (RingHom.mem_ker.mpr hy))

theorem extendAtPoint_toMap (s : ℂ) (g : A →+* LocalAt s)
    (hg : (residue s).comp g = pointMap s) (x : A) :
    extendAtPoint s g hg (algebraMap A (LocalAt s) x) = g x := by
  simp [extendAtPoint]

#print axioms residue_surjective
#print axioms extendAtPoint_toMap
end BChartTransport
