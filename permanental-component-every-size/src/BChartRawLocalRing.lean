import BChartAmbientTransport
import Mathlib.RingTheory.Localization.LocalizationLocalization

set_option autoImplicit false
namespace BChartTransport
open PermanentGauge PermanentGauge.Coordinates

noncomputable def rawPointIdeal (s : ℂ) : Ideal P25 := RingHom.ker (pointPoly s)
instance rawPointIdeal_prime (s : ℂ) : (rawPointIdeal s).IsPrime :=
  RingHom.ker_isPrime (pointPoly s)
abbrev RawLocalAt (s : ℂ) := Localization.AtPrime (rawPointIdeal s)

theorem rawPointIdeal_comap (s : ℂ) :
    rawPointIdeal s = (pointIdeal s).comap (algebraMap P25 A) := by
  change RingHom.ker (pointPoly s) = RingHom.ker ((pointMap s).comp (algebraMap P25 A))
  simp [pointMap]

noncomputable instance rawLocalization (s : ℂ) :
    IsLocalization.AtPrime (LocalAt s) (rawPointIdeal s) := by
  change IsLocalization (rawPointIdeal s).primeCompl (LocalAt s)
  have he : (rawPointIdeal s).primeCompl =
      ((pointIdeal s).comap (algebraMap P25 A)).primeCompl := by
    ext p
    change p ∉ rawPointIdeal s ↔ p ∉ (pointIdeal s).comap (algebraMap P25 A)
    rw [rawPointIdeal_comap]
  rw [he]
  infer_instance

/-- Canonical identification of the raw polynomial local ring with the
previously used open-chart local ring. -/
noncomputable def rawLocalEquiv (s : ℂ) : RawLocalAt s ≃ₐ[P25] LocalAt s :=
  IsLocalization.algEquiv (rawPointIdeal s).primeCompl _ _

theorem rawLocalEquiv_polynomial (s : ℂ) (p : P25) :
    rawLocalEquiv s (algebraMap P25 (RawLocalAt s) p) = toFamilyLocal s p := by
  exact (rawLocalEquiv s).commutes p

noncomputable def rawMatrix : Matrix (Fin 5) (Fin 5) P25 := fun i j => v i j
noncomputable def rawLocalCofactorIdeal (s : ℂ) : Ideal (RawLocalAt s) :=
  Ideal.map (algebraMap P25 (RawLocalAt s)) (cofactorIdeal rawMatrix)

theorem rawLocalEquiv_cofactorIdeal (s : ℂ) :
    Ideal.map (rawLocalEquiv s).toRingHom (rawLocalCofactorIdeal s) =
      localAmbientIdeal s := by
  rw [rawLocalCofactorIdeal, Ideal.map_map]
  have he : (rawLocalEquiv s).toRingHom.comp (algebraMap P25 (RawLocalAt s)) =
      (algebraMap A (LocalAt s)).comp (algebraMap P25 A) := by
    apply RingHom.ext
    intro p
    exact rawLocalEquiv_polynomial s p
  rw [he, ← Ideal.map_map, cofactorIdeal_map]
  rfl

noncomputable def rawAmbientChartEquiv (s : ℂ) (hs : s ≠ 0) :
    RawLocalAt s ≃+* LocalAt s :=
  (rawLocalEquiv s).toRingEquiv.trans (ambientChartEquiv s hs)

/-- Exact local normal form for the original 25-variable cofactor ideal,
localized directly at A(s), not merely a slice or an assumed correspondence. -/
theorem raw_ambient_cofactor_normal_form (s : ℂ) (hs : s ≠ 0) :
    Ideal.map (rawAmbientChartEquiv s hs).toRingHom (rawLocalCofactorIdeal s) =
      localExpectedIdeal s := by
  change Ideal.map ((ambientChartEquiv s hs).toRingHom.comp
    (rawLocalEquiv s).toRingHom) (rawLocalCofactorIdeal s) = _
  rw [← Ideal.map_map, rawLocalEquiv_cofactorIdeal, ambient_cofactor_normal_form s hs]

#print axioms rawLocalEquiv
#print axioms raw_ambient_cofactor_normal_form
end BChartTransport
