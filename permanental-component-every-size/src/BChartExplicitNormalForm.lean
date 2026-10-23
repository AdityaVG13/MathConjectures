import BChartRawLocalRing

set_option autoImplicit false
namespace BChartTransport
open PermanentGauge PermanentGauge.Coordinates

/-- Twelve transverse affine errors and three squarefree products.
The nine pivot entries and the parameter direction remain free. -/
noncomputable def explicitGenerator (s : ℂ) : Fin 15 → P25 :=
  ![v 1 1, v 1 2 + 1, v 1 4, v 2 2 - 1, v 2 3 - 1, v 2 4,
    v 3 0 - MvPolynomial.C s, v 2 1 + 1, v 3 2 - MvPolynomial.C s,
    v 4 1, v 4 2 - MvPolynomial.C s, v 4 4 + 1,
    v 0 4 * v 1 3, v 0 4 * v 3 1, v 1 3 * v 3 1]

noncomputable def explicitTarget (s : ℂ) : Ideal P25 :=
  Ideal.span (Set.range (explicitGenerator s))

theorem explicitGenerator_correspondence (s : ℂ) (k : Fin 15) :
    chartMap s (ConcreteLocalGeometry.targetGenerator k) = explicitGenerator s k := by
  fin_cases k <;>
    simp [chartMap, ConcreteLocalGeometry.targetGenerator, ConcreteLocalGeometry.x,
      assignment, explicitGenerator]

theorem explicitTarget_correspondence (s : ℂ) :
    Ideal.map (chartMap s) ConcreteLocalGeometry.targetIdeal = explicitTarget s := by
  rw [ConcreteLocalGeometry.targetIdeal, Ideal.map_span, ← Set.range_comp]
  have he : chartMap s ∘ ConcreteLocalGeometry.targetGenerator = explicitGenerator s := by
    funext k
    exact explicitGenerator_correspondence s k
  rw [he]
  rfl

/-- Direct original-matrix statement with the target generators expanded.
This is an equality of ideals under a proved local ring equivalence, not a
finite jet comparison or numerical agreement. -/
theorem raw_ambient_explicit_normal_form (s : ℂ) (hs : s ≠ 0) :
    Ideal.map (rawAmbientChartEquiv s hs).toRingHom (rawLocalCofactorIdeal s) =
      Ideal.map (toFamilyLocal s) (explicitTarget s) := by
  rw [raw_ambient_cofactor_normal_form s hs, localExpectedIdeal,
    explicitTarget_correspondence]

#print axioms explicitTarget_correspondence
#print axioms raw_ambient_explicit_normal_form
end BChartTransport
