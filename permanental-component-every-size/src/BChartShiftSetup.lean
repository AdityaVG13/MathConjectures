import BChartLocalResidue

set_option autoImplicit false
namespace BChartTransport
open PermanentGauge PermanentGauge.Coordinates

noncomputable def raw (s : ℂ) (i j : Fin 5) : LocalAt s := toFamilyLocal s (v i j)
noncomputable def scalar (s c : ℂ) : LocalAt s := toFamilyLocal s (MvPolynomial.C c)
noncomputable def denominatorUnit (s : ℂ) (hs : s ≠ 0) : (LocalAt s)ˣ :=
  (denominator_local_unit s hs).unit

theorem denominatorUnit_value (s : ℂ) (hs : s ≠ 0) :
    (denominatorUnit s hs : LocalAt s) = toFamilyLocal s denominator :=
  (denominator_local_unit s hs).unit_spec

theorem residue_denominatorUnit (s : ℂ) (hs : s ≠ 0) :
    residue s (denominatorUnit s hs : LocalAt s) = s := by
  rw [denominatorUnit_value, residue_polynomial, denominator_value]

theorem residue_denominatorInverse (s : ℂ) (hs : s ≠ 0) :
    residue s (((denominatorUnit s hs)⁻¹ : (LocalAt s)ˣ) : LocalAt s) = s⁻¹ := by
  have hm : residue s (denominatorUnit s hs : LocalAt s) *
      residue s (((denominatorUnit s hs)⁻¹ : (LocalAt s)ˣ) : LocalAt s) = 1 := by
    rw [← map_mul]
    simp
  rw [residue_denominatorUnit] at hm
  apply mul_left_cancel₀ hs
  rw [hm, mul_inv_cancel₀ hs]

noncomputable def jNumerator : P25 :=
  v 4 0*(1+v 0 4)*(v 4 0*(1-v 3 1))*(1+v 4 0*v 1 3)
noncomputable def zNumerator : P25 :=
  v 4 0*(1+v 1 3)*(v 4 0*(1-v 3 1))*(1-(v 4 0+1)*v 0 4)
noncomputable def qNumerator : P25 :=
  -v 3 1*(1+2*v 4 0)*(1-(v 4 0+1)*v 0 4)*(1+v 4 0*v 1 3)
noncomputable def jValue (s : ℂ) (hs : s ≠ 0) : LocalAt s :=
  toFamilyLocal s jNumerator * (((denominatorUnit s hs)⁻¹ : (LocalAt s)ˣ) : LocalAt s)
noncomputable def zValue (s : ℂ) (hs : s ≠ 0) : LocalAt s :=
  toFamilyLocal s zNumerator * (((denominatorUnit s hs)⁻¹ : (LocalAt s)ˣ) : LocalAt s)
noncomputable def qValue (s : ℂ) (hs : s ≠ 0) : LocalAt s :=
  toFamilyLocal s qNumerator * (((denominatorUnit s hs)⁻¹ : (LocalAt s)ˣ) : LocalAt s)

theorem residue_jValue (s : ℂ) (hs : s ≠ 0) : residue s (jValue s hs) = s := by
  simp [jValue, residue_polynomial, residue_denominatorUnit, pointPoly,
    jNumerator, v, PrimitiveFamily.A, mul_assoc, hs]
theorem residue_zValue (s : ℂ) (hs : s ≠ 0) : residue s (zValue s hs) = s := by
  simp [zValue, residue_polynomial, residue_denominatorUnit, pointPoly,
    zNumerator, v, PrimitiveFamily.A, mul_assoc, hs]
theorem residue_qValue (s : ℂ) (hs : s ≠ 0) : residue s (qValue s hs) = 0 := by
  simp [qValue, residue_polynomial, pointPoly, qNumerator, v, PrimitiveFamily.A]

/-- The eight nonzero shifts of the triangular b-chart reconstruction.
Their coefficients depend only on the four retained base coordinates. -/
noncomputable def shift (s : ℂ) (hs : s ≠ 0) : Matrix (Fin 5) (Fin 5) (LocalAt s) :=
  !![0,0,0,0,0;
     0,0,-raw s 1 3,0,0;
     0,qValue s hs,0,-qValue s hs,raw s 0 4;
     jValue s hs-scalar s s,0,jValue s hs+zValue s hs-raw s 4 0-scalar s s,0,0;
     0,raw s 3 1,zValue s hs-scalar s s,0,0]

def baseIndex : Fin 4 → Index := ![(4,0),(0,4),(1,3),(3,1)]

theorem shift_at_pivot (s : ℂ) (hs : s ≠ 0) (k : Fin 9) :
    shift s hs (pivot k).1 (pivot k).2 = 0 := by
  fin_cases k <;> simp [shift, pivot]

theorem shift_at_base (s : ℂ) (hs : s ≠ 0) (k : Fin 4) :
    shift s hs (baseIndex k).1 (baseIndex k).2 = 0 := by
  fin_cases k <;> simp [shift, baseIndex]

theorem residue_shift (s : ℂ) (hs : s ≠ 0) (i j : Fin 5) :
    residue s (shift s hs i j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [shift, raw, scalar, residue_jValue, residue_zValue, residue_qValue,
      residue_polynomial, pointPoly, v, PrimitiveFamily.A]

#print axioms residue_shift
#print axioms shift_at_base
end BChartTransport
