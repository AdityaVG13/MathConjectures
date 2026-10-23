import GeometryBridge.UpperQuadraticGeometry
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.TensorProduct.Basis

namespace UniformUpperPolynomial
noncomputable section
open UniformUpperQuadratic
open scoped TensorProduct

abbrev PolyBase (N : ℕ) := MvPolynomial (Fin N) Base
abbrev PolyChart (N : ℕ) := MvPolynomial (Fin N) Chart

instance coefficientAlgebra (N : ℕ) : Algebra (PolyBase N) (PolyChart N) :=
  MvPolynomial.algebraMvPolynomial

/-- The actual coefficient-extension polynomial algebra is the base change of Chart. -/
def coefficientBaseChange (N : ℕ) :
    PolyBase N ⊗[Base] Chart ≃ₐ[PolyBase N] PolyChart N :=
  Algebra.IsPushout.equiv Base (PolyBase N) Chart (PolyChart N)

instance polyChart_free (N : ℕ) : Module.Free (PolyBase N) (PolyChart N) :=
  Module.Free.of_equiv (coefficientBaseChange N).toLinearEquiv

instance polyChart_finite (N : ℕ) : Module.Finite (PolyBase N) (PolyChart N) :=
  Module.Finite.equiv (coefficientBaseChange N).toLinearEquiv

instance polyChart_flat (N : ℕ) : Module.Flat (PolyBase N) (PolyChart N) := inferInstance
instance polyChart_integral (N : ℕ) : Algebra.IsIntegral (PolyBase N) (PolyChart N) := inferInstance

theorem polyBase_dimension (N : ℕ) : ringKrullDim (PolyBase N) = (N+2 : ℕ) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, base_dimension]
  simp [Nat.cast_add, add_comm]

theorem polyChart_component_dimension (N : ℕ) (Q : Ideal (PolyChart N))
    (hQ : IsMinimalPrime Q) : ringKrullDim (PolyChart N ⧸ Q) = (N+2 : ℕ) := by
  rw [UniformComponentGeometry.ringKrullDim_minimalPrime_quotient (R := PolyBase N) Q hQ,
    polyBase_dimension]

instance polyChart_smooth (N : ℕ) : Algebra.Smooth ℂ (PolyChart N) := by
  letI : Algebra.Smooth Chart (PolyChart N) := ⟨inferInstance, inferInstance⟩
  exact Algebra.Smooth.comp ℂ Chart (PolyChart N)

#print axioms coefficientBaseChange
#print axioms polyChart_component_dimension
#print axioms polyChart_smooth
end
end UniformUpperPolynomial
