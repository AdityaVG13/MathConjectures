import BChartShiftSetup

set_option autoImplicit false
namespace BChartTransport
open PermanentGauge PermanentGauge.Coordinates MvPolynomial

noncomputable def translationImage (s : ℂ) (hs : s ≠ 0) (n : ℤ) (ij : Index) : LocalAt s :=
  raw s ij.1 ij.2 + (n : LocalAt s) * shift s hs ij.1 ij.2
noncomputable def translationPoly (s : ℂ) (hs : s ≠ 0) (n : ℤ) : P25 →+* LocalAt s :=
  eval₂Hom ((toFamilyLocal s).comp C) (translationImage s hs n)

theorem translationImage_pivot (s : ℂ) (hs : s ≠ 0) (n : ℤ) (k : Fin 9) :
    translationImage s hs n (pivot k) = raw s (pivot k).1 (pivot k).2 := by
  simp [translationImage, shift_at_pivot]

theorem translationPoly_delta (s : ℂ) (hs : s ≠ 0) (n : ℤ) :
    translationPoly s hs n delta = toFamilyLocal s delta := by
  simp [delta, translationPoly, translationImage_pivot, raw, v]

theorem delta_local_unit (s : ℂ) : IsUnit (toFamilyLocal s delta) := by
  exact (IsLocalization.Away.algebraMap_isUnit delta (S := A)).map
    (algebraMap A (LocalAt s))

noncomputable def translationOpen (s : ℂ) (hs : s ≠ 0) (n : ℤ) : A →+* LocalAt s :=
  IsLocalization.Away.lift delta (show IsUnit (translationPoly s hs n delta) by
    rw [translationPoly_delta]
    exact delta_local_unit s)

theorem translationOpen_matrix (s : ℂ) (hs : s ≠ 0) (n : ℤ) (i j : Fin 5) :
    translationOpen s hs n (matrix i j) = translationImage s hs n (i,j) := by
  simp [translationOpen, matrix, translationPoly]

theorem translationOpen_constant (s : ℂ) (hs : s ≠ 0) (n : ℤ) (c : ℂ) :
    translationOpen s hs n (algebraMap P25 A (C c)) = scalar s c := by
  simp [translationOpen, translationPoly, scalar]

theorem residue_translationImage (s : ℂ) (hs : s ≠ 0) (n : ℤ) (ij : Index) :
    residue s (translationImage s hs n ij) = PrimitiveFamily.A s ij.1 ij.2 := by
  simp [translationImage, residue_shift, raw, residue_polynomial, pointPoly, v]

theorem residue_translationOpen (s : ℂ) (hs : s ≠ 0) (n : ℤ) :
    (residue s).comp (translationOpen s hs n) = pointMap s := by
  apply IsLocalization.ringHom_ext (Submonoid.powers delta)
  apply MvPolynomial.ringHom_ext
  · intro c
    change residue s (translationOpen s hs n (algebraMap P25 A (C c))) =
      pointMap s (algebraMap P25 A (C c))
    rw [translationOpen_constant]
    simp [scalar, residue_polynomial, pointMap, pointPoly]
  · intro ij
    change residue s (translationOpen s hs n (matrix ij.1 ij.2)) = pointMap s (matrix ij.1 ij.2)
    rw [translationOpen_matrix, pointMap_matrix]
    exact residue_translationImage s hs n ij

/-- An actual endomorphism of the family local ring. Inverse/group laws are
not part of this construction and must be proved separately. -/
noncomputable def translationMap (s : ℂ) (hs : s ≠ 0) (n : ℤ) : LocalAt s →+* LocalAt s :=
  extendAtPoint s (translationOpen s hs n) (residue_translationOpen s hs n)

theorem translationMap_raw (s : ℂ) (hs : s ≠ 0) (n : ℤ) (i j : Fin 5) :
    translationMap s hs n (raw s i j) = raw s i j + (n : LocalAt s)*shift s hs i j := by
  change translationMap s hs n (algebraMap A (LocalAt s) (matrix i j)) = _
  rw [translationMap, extendAtPoint_toMap, translationOpen_matrix]
  rfl

theorem translationMap_scalar (s : ℂ) (hs : s ≠ 0) (n : ℤ) (c : ℂ) :
    translationMap s hs n (scalar s c) = scalar s c := by
  change translationMap s hs n (algebraMap A (LocalAt s) (algebraMap P25 A (C c))) = _
  rw [translationMap, extendAtPoint_toMap, translationOpen_constant]

theorem translationMap_base (s : ℂ) (hs : s ≠ 0) (n : ℤ) (k : Fin 4) :
    translationMap s hs n (raw s (baseIndex k).1 (baseIndex k).2) =
      raw s (baseIndex k).1 (baseIndex k).2 := by
  rw [translationMap_raw, shift_at_base]
  simp

#print axioms translationMap
#print axioms translationMap_raw
end BChartTransport
