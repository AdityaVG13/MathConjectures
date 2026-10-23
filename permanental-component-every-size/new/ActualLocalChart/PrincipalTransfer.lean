import ActualLocalChart.Spread
import Mathlib.RingTheory.Localization.Away.Basic

namespace UniformComponentGeometry
noncomputable section

/-- Localization of a quotient is the quotient of the localized ambient ring. -/
def quotientAwayEquiv {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (I : Ideal R) (s : R) :
    Localization.Away (algebraMap R (R ⧸ I) s) ≃ₐ[K]
      (Localization.Away s ⧸ I.map (algebraMap R (Localization.Away s))) := by
  let T := Localization.Away s ⧸ I.map (algebraMap R (Localization.Away s))
  haveI : IsLocalization.Away (algebraMap R (R ⧸ I) s) T := by
    rw [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
    infer_instance
  haveI : IsScalarTower K (R ⧸ I) T :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change Ideal.Quotient.mk _ (algebraMap K (Localization.Away s) x) =
        Ideal.Quotient.mk _ (algebraMap R (Localization.Away s) (algebraMap K R x))
      rw [IsScalarTower.algebraMap_apply K R (Localization.Away s)])
  exact (IsLocalization.algEquiv
    (Submonoid.powers (algebraMap R (R ⧸ I) s)) _ T).restrictScalars K

/-- Equality on one ambient principal open persists after shrinking it. -/
theorem ideal_map_eq_on_product {R : Type*} [CommRing R]
    (I J : Ideal R) (s g : R)
    (h : I.map (algebraMap R (Localization.Away s)) =
      J.map (algebraMap R (Localization.Away s))) :
    I.map (algebraMap R (Localization.Away (s*g))) =
      J.map (algebraMap R (Localization.Away (s*g))) := by
  let f : Localization.Away s →+* Localization.Away (s*g) :=
    IsLocalization.Away.awayToAwayRight s g
  have hf : f.comp (algebraMap R (Localization.Away s)) =
      algebraMap R (Localization.Away (s*g)) := by
    ext x
    exact IsLocalization.Away.awayToAwayRight_eq s g x
  have he := congrArg (Ideal.map f) h
  simpa only [Ideal.map_map, hf] using he

/-- Scheme-theoretic ideal equality on an ambient open gives the actual quotient
algebra equivalence on any smaller product open. -/
def quotientAwayProductEquiv {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (I J : Ideal R) (s g : R)
    (h : I.map (algebraMap R (Localization.Away s)) =
      J.map (algebraMap R (Localization.Away s))) :
    Localization.Away (algebraMap R (R ⧸ I) (s*g)) ≃ₐ[K]
      Localization.Away (algebraMap R (R ⧸ J) (s*g)) :=
  (quotientAwayEquiv I (s*g)).trans
    ((Ideal.quotientEquivAlgOfEq K (ideal_map_eq_on_product I J s g h)).trans
      (quotientAwayEquiv J (s*g)).symm)

/-- The product open is the further principal open inside the given chart. -/
def quotientAwayIteratedEquiv {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (I J : Ideal R) (s g : R)
    (h : I.map (algebraMap R (Localization.Away s)) =
      J.map (algebraMap R (Localization.Away s))) :
    Localization.Away (algebraMap R (R ⧸ I) (s*g)) ≃ₐ[K]
      Localization.Away (algebraMap (R ⧸ J)
        (Localization.Away (algebraMap R (R ⧸ J) g)) (algebraMap R (R ⧸ J) s)) := by
  let T := Localization.Away (algebraMap (R ⧸ J)
    (Localization.Away (algebraMap R (R ⧸ J) g)) (algebraMap R (R ⧸ J) s))
  haveI : IsLocalization.Away (algebraMap R (R ⧸ J) (s*g)) T := by
    rw [map_mul]
    infer_instance
  exact (quotientAwayProductEquiv I J s g h).trans
    ((IsLocalization.algEquiv (Submonoid.powers (algebraMap R (R ⧸ J) (s*g)))
      _ T).restrictScalars K)

end
end UniformComponentGeometry

#print axioms UniformComponentGeometry.quotientAwayIteratedEquiv
