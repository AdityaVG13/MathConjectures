import PrimitiveFamily
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic

/-! Concrete setup for the local ideal equality. This file does not assume or
claim that the critical ideal equals the target ideal. It constructs the actual
local ring from the proved maximal evaluation kernel and proves the denominator
is a unit there. -/
namespace ConcreteLocalGeometry
abbrev P := MvPolynomial (Fin 16) ℂ
noncomputable def x (i : Fin 16) : P := MvPolynomial.X i
noncomputable def t : P := MvPolynomial.C (2 : ℂ) + x 0
noncomputable def da : P := 1 - (t + 1) * x 1
noncomputable def dq : P := 1 + MvPolynomial.C (2 : ℂ)*t - t*x 3
noncomputable def dd : P := 1 + t*x 2
noncomputable def den : P := da*dq*dd
noncomputable def jn : P := t*(1+x 1)*dq*dd
noncomputable def kn : P := -t*x 3*da*dd
noncomputable def zn : P := t*(1+x 2)*da*dq
noncomputable def N : Matrix (Fin 5) (Fin 5) P :=
  !![1,1,1,1,x 1;
     1,x 4,-1-x 2+x 5,x 2,x 6;
     1,x 3-1,1+x 7,1-x 3+x 8,x 1+x 9;
     jn+den*x 10,kn+den*x 11,jn+zn-t*den+den*x 12,den,den;
     t*den,kn+den*x 13,zn+den*x 14,den,-den+den*x 15]
noncomputable def equation (ij : Fin 5 × Fin 5) : P :=
  (N.submatrix ij.1.succAbove ij.2.succAbove).permanent
noncomputable def targetGenerator : Fin 15 → P :=
  ![x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,
    x 1*x 2,x 1*x 3,x 2*x 3]
noncomputable def criticalIdeal : Ideal P := Ideal.span (Set.range equation)
noncomputable def targetIdeal : Ideal P := Ideal.span (Set.range targetGenerator)
noncomputable def evalOrigin : P →+* ℂ :=
  MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun _ => 0)
noncomputable def origin : Ideal P := RingHom.ker evalOrigin

theorem evalOrigin_surjective : Function.Surjective evalOrigin := by
  intro c
  exact ⟨MvPolynomial.C c, by simp [evalOrigin]⟩

instance origin_maximal : origin.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective evalOrigin evalOrigin_surjective

noncomputable abbrev Local := Localization.AtPrime origin

noncomputable def localCritical : Ideal Local :=
  Ideal.map (algebraMap P Local) criticalIdeal
noncomputable def localTarget : Ideal Local :=
  Ideal.map (algebraMap P Local) targetIdeal

theorem denominator_value : evalOrigin den = 5 := by
  norm_num [evalOrigin, den, da, dq, dd, t, x]

theorem denominator_not_mem : den ∉ origin := by
  intro h
  have hz : evalOrigin den = 0 := RingHom.mem_ker.mp h
  rw [denominator_value] at hz
  norm_num at hz

theorem denominator_unit : IsUnit (algebraMap P Local den) := by
  exact IsLocalization.map_units Local (⟨den, denominator_not_mem⟩ : origin.primeCompl)

#print axioms denominator_unit
#print axioms origin_maximal
end ConcreteLocalGeometry
