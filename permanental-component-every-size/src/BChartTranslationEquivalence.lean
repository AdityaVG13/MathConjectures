import BChartTranslationFixed

set_option autoImplicit false
namespace BChartTransport
open PermanentGauge.Coordinates MvPolynomial

/-- Extensionality on the actual twice-localized coordinate ring. -/
theorem localHom_ext (s : ℂ) (f g : LocalAt s →+* LocalAt s)
    (hC : ∀ c : ℂ, f (scalar s c) = g (scalar s c))
    (hX : ∀ i j : Fin 5, f (raw s i j) = g (raw s i j)) : f = g := by
  apply IsLocalization.ringHom_ext (pointIdeal s).primeCompl
  apply IsLocalization.ringHom_ext (Submonoid.powers delta)
  apply MvPolynomial.ringHom_ext
  · intro c
    exact hC c
  · intro ij
    exact hX ij.1 ij.2

theorem translationMap_zero (s : ℂ) (hs : s ≠ 0) :
    translationMap s hs 0 = RingHom.id (LocalAt s) := by
  apply localHom_ext s
  · intro c
    simp [translationMap_scalar]
  · intro i j
    simp [translationMap_raw]

theorem translationMap_add (s : ℂ) (hs : s ≠ 0) (m n : ℤ) :
    (translationMap s hs m).comp (translationMap s hs n) = translationMap s hs (m+n) := by
  apply localHom_ext s
  · intro c
    simp [translationMap_scalar]
  · intro i j
    simp only [RingHom.comp_apply, translationMap_raw, map_add, map_mul,
      map_intCast, translationMap_shift, Int.cast_add]
    ring

/-- The genuine triangular b-chart local coordinate automorphism. The inverse
subtracts the same shifts, whose invariance has been proved separately. -/
noncomputable def translationEquiv (s : ℂ) (hs : s ≠ 0) (n : ℤ) : LocalAt s ≃+* LocalAt s :=
  { translationMap s hs n with
    invFun := translationMap s hs (-n)
    left_inv := by
      intro x
      have he := RingHom.congr_fun (translationMap_add s hs (-n) n) x
      simpa [translationMap_zero] using he
    right_inv := by
      intro x
      have he := RingHom.congr_fun (translationMap_add s hs n (-n)) x
      simpa [translationMap_zero] using he }

#print axioms localHom_ext
#print axioms translationEquiv
end BChartTransport
