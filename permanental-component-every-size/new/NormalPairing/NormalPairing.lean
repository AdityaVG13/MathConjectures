import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic

set_option autoImplicit false

namespace ComponentNormalPairing

variable {K ι H : Type*} [Field K] [Fintype ι] [DecidableEq ι]
  [AddCommGroup H] [Module K H]

/-- A hyperbolic pairing remains nondegenerate after adding an arbitrary bilinear
form on its first half and the residual space, provided the residual restriction
is nondegenerate. This is a general linear-algebra lemma, not an identification
of the actual permanental Hessian. -/
theorem radical_zero
    (Q : LinearMap.BilinForm K ((ι → K) × H))
    (hQ : ∀ h : H, (∀ k : H, Q (0, h) (0, k) = 0) → h = 0)
    (x y : ι → K) (h : H)
    (hz : ∀ (u v : ι → K) (k : H),
      (∑ i, x i * v i) + (∑ i, u i * y i) + Q (x, h) (u, k) = 0) :
    x = 0 ∧ y = 0 ∧ h = 0 := by
  have hx : x = 0 := by
    funext i
    have hi := hz 0 (Pi.single i 1) 0
    change (∑ j, x j * (Pi.single i (1 : K) : ι → K) j) + (∑ j, (0 : ι → K) j * y j) + Q (x, h) 0 = 0 at hi
    simpa [Pi.single_apply, mul_ite] using hi
  have hh : h = 0 := by
    apply hQ
    intro k
    have hk := hz 0 0 k
    simpa [hx] using hk
  have hy : y = 0 := by
    funext i
    have hi := hz (Pi.single i 1) 0 0
    rw [hx, hh] at hi
    change (∑ j, (0 : ι → K) j * (0 : ι → K) j) + (∑ j, (Pi.single i (1 : K) : ι → K) j * y j) + Q 0 (Pi.single i 1, 0) = 0 at hi
    simpa [Pi.single_apply, ite_mul] using hi
  exact ⟨hx, hy, hh⟩

section Saddle
variable {V F : Type*} [AddCommGroup V] [Module K V] [AddCommGroup F] [Module K F]

/-- A general saddle bilinear form is nondegenerate once its cross-pairing is
injective and its residual restriction on the annihilator is nondegenerate.
This lemma does not assume an ambient Hessian has this form. -/
theorem saddle_kernel_zero
    (A : V →ₗ[K] F →ₗ[K] K) (hA : Function.Injective A)
    (Q : LinearMap.BilinForm K F)
    (hQ : ∀ x : F, (∀ v : V, A v x = 0) →
      (∀ y : F, (∀ v : V, A v y = 0) → Q x y = 0) → x = 0)
    (v : V) (x : F)
    (h : ∀ (w : V) (y : F), A v y + A w x + Q x y = 0) : v = 0 ∧ x = 0 := by
  have hxker (w : V) : A w x = 0 := by simpa using h w 0
  have hx : x = 0 := by
    apply hQ x hxker
    intro y hy
    have hh := h 0 y
    simpa [hy v] using hh
  have hv : A v = 0 := by
    ext y
    have hh := h 0 y
    simpa [hx] using hh
  exact ⟨hA (by simpa using hv), hx⟩
end Saddle

#print axioms saddle_kernel_zero
#print axioms radical_zero
end ComponentNormalPairing
