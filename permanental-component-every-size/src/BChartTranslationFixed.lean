import BChartTranslationMaps

set_option autoImplicit false
namespace BChartTransport
open PermanentGauge.Coordinates

noncomputable def rationalData (s : ℂ) : Fin 4 → LocalAt s :=
  ![toFamilyLocal s denominator,toFamilyLocal s jNumerator,
    toFamilyLocal s zNumerator,toFamilyLocal s qNumerator]

theorem translationMap_data (s : ℂ) (hs : s ≠ 0) (n : ℤ) (k : Fin 4) :
    translationMap s hs n (rationalData s k) = rationalData s k := by
  have ht : translationMap s hs n (toFamilyLocal s (v 4 0)) = toFamilyLocal s (v 4 0) := by
    simpa [baseIndex, raw] using translationMap_base s hs n 0
  have ha : translationMap s hs n (toFamilyLocal s (v 0 4)) = toFamilyLocal s (v 0 4) := by
    simpa [baseIndex, raw] using translationMap_base s hs n 1
  have hd : translationMap s hs n (toFamilyLocal s (v 1 3)) = toFamilyLocal s (v 1 3) := by
    simpa [baseIndex, raw] using translationMap_base s hs n 2
  have hb : translationMap s hs n (toFamilyLocal s (v 3 1)) = toFamilyLocal s (v 3 1) := by
    simpa [baseIndex, raw] using translationMap_base s hs n 3
  have h2a : toFamilyLocal s (2 : P25) = 2 := by
    rw [show (2 : P25) = 1+1 by ring, map_add, map_one]
    all_goals ring
  have h2b : translationMap s hs n (2 : LocalAt s) = 2 := by
    rw [show (2 : LocalAt s) = 1+1 by ring, map_add, map_one]
  fin_cases k <;>
    simp [rationalData, denominator, jNumerator, zNumerator, qNumerator,
      ht, ha, hd, hb, h2a, h2b]

theorem translationMap_denominatorUnit (s : ℂ) (hs : s ≠ 0) (n : ℤ) :
    Units.map (translationMap s hs n : LocalAt s →* LocalAt s) (denominatorUnit s hs) =
      denominatorUnit s hs := by
  apply Units.ext
  change translationMap s hs n (denominatorUnit s hs : LocalAt s) = (denominatorUnit s hs : LocalAt s)
  rw [denominatorUnit_value]
  simpa [rationalData] using translationMap_data s hs n 0

theorem translationMap_denominatorInverse (s : ℂ) (hs : s ≠ 0) (n : ℤ) :
    translationMap s hs n (((denominatorUnit s hs)⁻¹ : (LocalAt s)ˣ) : LocalAt s) =
      (((denominatorUnit s hs)⁻¹ : (LocalAt s)ˣ) : LocalAt s) := by
  have he : Units.map (translationMap s hs n : LocalAt s →* LocalAt s)
      ((denominatorUnit s hs)⁻¹) = (denominatorUnit s hs)⁻¹ := by
    rw [map_inv, translationMap_denominatorUnit]
  exact congrArg (fun u : (LocalAt s)ˣ => (u : LocalAt s)) he

theorem translationMap_jValue (s : ℂ) (hs : s ≠ 0) (n : ℤ) :
    translationMap s hs n (jValue s hs) = jValue s hs := by
  have he := translationMap_data s hs n 1
  simp [rationalData] at he
  simp [jValue, he, translationMap_denominatorInverse]
theorem translationMap_zValue (s : ℂ) (hs : s ≠ 0) (n : ℤ) :
    translationMap s hs n (zValue s hs) = zValue s hs := by
  have he := translationMap_data s hs n 2
  simp [rationalData] at he
  simp [zValue, he, translationMap_denominatorInverse]
theorem translationMap_qValue (s : ℂ) (hs : s ≠ 0) (n : ℤ) :
    translationMap s hs n (qValue s hs) = qValue s hs := by
  have he := translationMap_data s hs n 3
  simp [rationalData] at he
  simp [qValue, he, translationMap_denominatorInverse]

/-- The actual rational shifts are fixed, because they use only the four
retained coordinates and a proved invertible denominator. -/
theorem translationMap_shift (s : ℂ) (hs : s ≠ 0) (n : ℤ) (i j : Fin 5) :
    translationMap s hs n (shift s hs i j) = shift s hs i j := by
  have ht : translationMap s hs n (raw s 4 0) = raw s 4 0 := by
    simpa [baseIndex] using translationMap_base s hs n 0
  have ha : translationMap s hs n (raw s 0 4) = raw s 0 4 := by
    simpa [baseIndex] using translationMap_base s hs n 1
  have hd : translationMap s hs n (raw s 1 3) = raw s 1 3 := by
    simpa [baseIndex] using translationMap_base s hs n 2
  have hb : translationMap s hs n (raw s 3 1) = raw s 3 1 := by
    simpa [baseIndex] using translationMap_base s hs n 3
  fin_cases i <;> fin_cases j <;>
    simp [shift, translationMap_jValue, translationMap_zValue, translationMap_qValue,
      translationMap_scalar, ht, ha, hd, hb]

#print axioms translationMap_data
#print axioms translationMap_shift
end BChartTransport
