import BChartTranslationEquivalence
import CofactorFunctor

set_option autoImplicit false
namespace BChartTransport
open PermanentGauge PermanentGauge.Coordinates

noncomputable local instance (ij : Index) : Decidable (IsPivot ij) := Classical.propDecidable _

noncomputable def localNormalizedMatrix (s : ℂ) : Matrix (Fin 5) (Fin 5) (LocalAt s) :=
  fun i j => algebraMap A (LocalAt s) (clearPivots matrix i j)
noncomputable def translatedNormalizedMatrix (s : ℂ) (hs : s ≠ 0) : Matrix (Fin 5) (Fin 5) (LocalAt s) :=
  fun i j => translationMap s hs 1 (localNormalizedMatrix s i j)

theorem translated_entry (s : ℂ) (hs : s ≠ 0) (i j : Fin 5) :
    translatedNormalizedMatrix s hs i j =
      if IsPivot (i,j) then 1 else raw s i j + shift s hs i j := by
  classical
  by_cases h : IsPivot (i,j)
  · simp [translatedNormalizedMatrix, localNormalizedMatrix, clearPivots, h]
  · change translationMap s hs 1 (algebraMap A (LocalAt s) (clearPivots matrix i j)) = _
    simp only [clearPivots, ite_eq_right h]
    change translationMap s hs 1 (raw s i j) = _
    simp [translationMap_raw]

noncomputable def rowClearing (s : ℂ) (hs : s ≠ 0) : Fin 5 → (LocalAt s)ˣ :=
  ![1,1,denominatorUnit s hs,denominatorUnit s hs,denominatorUnit s hs]

noncomputable def clearedMatrixData (s : ℂ) : Matrix (Fin 5) (Fin 5) P25 :=
  !![1,1,1,1,v 0 4;
     1,v 1 1,v 1 2-v 1 3,v 1 3,v 1 4;
     denominator,qNumerator+denominator*v 2 1,denominator*v 2 2,
       denominator*v 2 3-qNumerator,denominator*(v 0 4+v 2 4);
     jNumerator+denominator*(v 3 0-MvPolynomial.C s),denominator*v 3 1,
       jNumerator+zNumerator-v 4 0*denominator+denominator*(v 3 2-MvPolynomial.C s),denominator,denominator;
     v 4 0*denominator,denominator*(v 3 1+v 4 1),
       zNumerator+denominator*(v 4 2-MvPolynomial.C s),denominator,denominator*v 4 4]

theorem clearedMatrix_eq_data (s : ℂ) : clearedMatrix s = clearedMatrixData s := rfl

theorem denominator_mul_jValue (s : ℂ) (hs : s ≠ 0) :
    toFamilyLocal s denominator * jValue s hs = toFamilyLocal s jNumerator := by
  rw [jValue, ← denominatorUnit_value s hs]
  simp [mul_comm]
theorem denominator_mul_zValue (s : ℂ) (hs : s ≠ 0) :
    toFamilyLocal s denominator * zValue s hs = toFamilyLocal s zNumerator := by
  rw [zValue, ← denominatorUnit_value s hs]
  simp [mul_comm]
theorem denominator_mul_qValue (s : ℂ) (hs : s ≠ 0) :
    toFamilyLocal s denominator * qValue s hs = toFamilyLocal s qNumerator := by
  rw [qValue, ← denominatorUnit_value s hs]
  simp [mul_comm]

/-- Exact matching of the actual transformed matrix and the previously proved
cleared chart, with all row multipliers proved units in this local ring. -/
theorem row_clearing_identity (s : ℂ) (hs : s ≠ 0) :
    scaleMatrix (fun i => (rowClearing s hs i : LocalAt s)) (fun _ => 1)
      (translatedNormalizedMatrix s hs) =
      (fun i j => toFamilyLocal s (clearedMatrix s i j)) := by
  classical
  apply Matrix.ext
  intro i j
  rw [clearedMatrix_eq_data]
  fin_cases i <;> fin_cases j <;>
    simp [scaleMatrix, rowClearing, translated_entry, IsPivot, pivot, Fin.exists_fin_succ,
      clearedMatrixData, shift, denominatorUnit_value, raw, scalar,
      mul_add, mul_sub, denominator_mul_jValue, denominator_mul_zValue,
      denominator_mul_qValue] <;>
    ring_nf <;> simp only [denominator_mul_qValue] <;> ring

theorem translated_cofactorIdeal (s : ℂ) (hs : s ≠ 0) :
    cofactorIdeal (translatedNormalizedMatrix s hs) = localClearedIdeal s := by
  have he := cofactorIdeal_scaleMatrix (rowClearing s hs) (fun _ => (1 : (LocalAt s)ˣ))
    (translatedNormalizedMatrix s hs)
  have hm : scaleMatrix (fun i => (rowClearing s hs i : LocalAt s))
      (fun j => ((fun _ : Fin 5 => (1 : (LocalAt s)ˣ)) j : LocalAt s))
      (translatedNormalizedMatrix s hs) =
      (fun i j => toFamilyLocal s (clearedMatrix s i j)) := row_clearing_identity s hs
  rw [hm] at he
  rw [localClearedIdeal, cofactorIdeal_map]
  exact he.symm

#print axioms row_clearing_identity
#print axioms translated_cofactorIdeal
end BChartTransport
