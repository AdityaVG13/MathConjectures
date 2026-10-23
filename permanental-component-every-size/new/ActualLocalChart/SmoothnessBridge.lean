import GeometryBridge.StandardSmoothBridge
import Mathlib.RingTheory.Localization.LocalizationLocalization

namespace UniformComponentGeometry
noncomputable section
variable {K A T σ ι : Type*} [CommRing K] [CommRing A] [CommRing T]
  [Algebra K A] [Finite σ] [Finite ι]

/-- Inverting the actual selected Jacobian of a genuine presentation makes it smooth. -/
theorem smooth_away_presentation_jacobian
    (P : Algebra.PreSubmersivePresentation K A σ ι) :
    Algebra.Smooth K (Localization.Away P.jacobian) := by
  let Δ := P.jacobian
  have hΔ : IsUnit (algebraMap A (Localization.Away Δ) Δ) :=
    IsLocalization.Away.algebraMap_isUnit _
  let Q : Algebra.SubmersivePresentation K (Localization.Away Δ) _ _ :=
    { toPreSubmersivePresentation :=
        .comp (.localizationAway (Localization.Away Δ) Δ) P
      jacobian_isUnit := by simpa [Algebra.smul_def, -isUnit_map_iff, hΔ] }
  letI := Q.isStandardSmooth
  infer_instance

/-- Any further localization containing the presentation Jacobian is formally smooth. -/
theorem formallySmooth_localization_of_jacobian_mem
    [Algebra A T] [Algebra K T] [IsScalarTower K A T]
    (P : Algebra.PreSubmersivePresentation K A σ ι) (M : Submonoid A)
    [IsLocalization M T] (hΔ : P.jacobian ∈ M) : Algebra.FormallySmooth K T := by
  let U := Localization.Away P.jacobian
  have hle : Submonoid.powers P.jacobian ≤ M := Submonoid.powers_le.mpr hΔ
  letI : Algebra U T := IsLocalization.localizationAlgebraOfSubmonoidLe U T _ M hle
  letI : IsScalarTower A U T :=
    IsLocalization.localization_isScalarTower_of_submonoid_le U T _ M hle
  letI : IsScalarTower K U T := IsScalarTower.to₁₃₄ K A U T
  letI : IsLocalization (M.map (algebraMap A U)) T :=
    IsLocalization.isLocalization_of_submonoid_le U T _ M hle
  letI : Algebra.Smooth K U := smooth_away_presentation_jacobian P
  letI : Algebra.FormallySmooth U T := Algebra.FormallySmooth.of_isLocalization (M.map (algebraMap A U))
  exact Algebra.FormallySmooth.comp K U T

#print axioms formallySmooth_localization_of_jacobian_mem
end
end UniformComponentGeometry
