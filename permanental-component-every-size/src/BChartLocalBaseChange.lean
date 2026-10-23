import BChartCoordinateCorrespondence
import BChartLocalEquality
import GaugeLocalTransport

set_option autoImplicit false

namespace BChartTransport
open PermanentGauge.Coordinates

noncomputable def intoOpen (s : ℂ) : ConcreteLocalGeometry.P →+* A :=
  (algebraMap P25 A).comp (chartMap s)

theorem point_after_intoOpen (s : ℂ) :
    (pointMap s).comp (intoOpen s) = ConcreteLocalGeometry.evalOrigin := by
  have hp : (pointMap s).comp (algebraMap P25 A) = pointPoly s := by
    simp [pointMap]
  rw [intoOpen, ← RingHom.comp_assoc, hp, point_composition]

theorem origin_comap_point (s : ℂ) :
    ConcreteLocalGeometry.origin = (pointIdeal s).comap (intoOpen s) := by
  change RingHom.ker ConcreteLocalGeometry.evalOrigin = RingHom.ker ((pointMap s).comp (intoOpen s))
  rw [point_after_intoOpen]

noncomputable def localChartMap (s : ℂ) : ConcreteLocalGeometry.Local →+* LocalAt s :=
  Localization.localRingHom ConcreteLocalGeometry.origin (pointIdeal s)
    (intoOpen s) (origin_comap_point s)

noncomputable def toFamilyLocal (s : ℂ) : P25 →+* LocalAt s :=
  (algebraMap A (LocalAt s)).comp (algebraMap P25 A)

theorem localChartMap_source (s : ℂ) :
    (localChartMap s).comp (algebraMap ConcreteLocalGeometry.P ConcreteLocalGeometry.Local) =
      (toFamilyLocal s).comp (chartMap s) := by
  apply RingHom.ext
  intro f
  exact Localization.localRingHom_to_map ConcreteLocalGeometry.origin (pointIdeal s)
    (intoOpen s) (origin_comap_point s) f

noncomputable def localClearedIdeal (s : ℂ) : Ideal (LocalAt s) :=
  Ideal.map (toFamilyLocal s) (PermanentGauge.cofactorIdeal (clearedMatrix s))
noncomputable def localExpectedIdeal (s : ℂ) : Ideal (LocalAt s) :=
  Ideal.map (toFamilyLocal s) (Ideal.map (chartMap s) ConcreteLocalGeometry.targetIdeal)

/-- Exact base change of the already verified b-chart local ideal equality.
This concerns the reconstructed cleared matrix, not yet the pivot-cleared raw
matrix before the pending triangular coordinate equivalence. -/
theorem localCleared_eq_expected (s : ℂ) (hs : s ≠ 0) :
    localClearedIdeal s = localExpectedIdeal s := by
  have he := congrArg (Ideal.map (localChartMap s))
    (BChartLocalGeometry.localCritical_eq_localTarget s hs)
  rw [BChartLocalGeometry.localCritical, ConcreteLocalGeometry.localTarget,
    Ideal.map_map, Ideal.map_map, localChartMap_source,
    ← Ideal.map_map, ← Ideal.map_map, ideal_correspondence] at he
  exact he

theorem denominator_value (s : ℂ) : pointPoly s denominator = s := by
  simp [pointPoly, denominator, v, PrimitiveFamily.A]

theorem denominator_local_unit (s : ℂ) (hs : s ≠ 0) :
    IsUnit (toFamilyLocal s denominator) := by
  have hn : algebraMap P25 A denominator ∉ pointIdeal s := by
    intro h
    have hz : pointMap s (algebraMap P25 A denominator) = 0 := RingHom.mem_ker.mp h
    have he : pointMap s (algebraMap P25 A denominator) = s := by
      simpa [pointMap] using denominator_value s
    exact hs (he.symm.trans hz)
  exact IsLocalization.map_units (LocalAt s)
    (⟨algebraMap P25 A denominator, hn⟩ : (pointIdeal s).primeCompl)

#print axioms localChartMap
#print axioms localCleared_eq_expected
#print axioms denominator_local_unit
end BChartTransport
