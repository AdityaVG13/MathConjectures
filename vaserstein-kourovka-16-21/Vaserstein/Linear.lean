import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Vaserstein.Basic

/-!
# General linear groups of vector spaces, blocks and frames

`GLV F V` is the group of invertible linear maps of `V`. This file provides the three
constructions the induction uses.

* `blk E` turns a pair `(a, b) ∈ GL(A) × GL(B)` into `a ⊕ b ∈ GL(V)` along a linear
  equivalence `E : V ≃ A × B`. It is a group homomorphism, and `isConj_blk` shows that the
  result only depends on `b` up to conjugation by a linear equivalence of the second factor.
* `restrictGL` restricts an invertible map to a subspace that it and its inverse preserve.
* A *frame* is a biorthogonal system: vectors `e j` and covectors `f i` with
  `f i (e j) = δ i j`. It gives `frameEquiv : V ≃ (Fin m → F) × K`, where `K` is the common
  kernel of the `f i`, and two frames of the same size give `frameTransport`, a linear
  equivalence carrying one frame to the other.
-/

namespace Vaserstein

open Module

/-- The group of invertible linear maps of `V`. -/
abbrev GLV (F V : Type*) [Field F] [AddCommGroup V] [Module F V] :=
  LinearMap.GeneralLinearGroup F V

variable {F : Type*} [Field F]

section GLV

variable {V : Type*} [AddCommGroup V] [Module F V]

@[simp] theorem GLV.apply_inv_apply (u : GLV F V) (x : V) :
    (u : V →ₗ[F] V) ((↑u⁻¹ : V →ₗ[F] V) x) = x := by
  rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]

@[simp] theorem GLV.inv_apply_apply (u : GLV F V) (x : V) :
    (↑u⁻¹ : V →ₗ[F] V) ((u : V →ₗ[F] V) x) = x := by
  rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]

@[simp] theorem GLV.mul_apply (u w : GLV F V) (x : V) :
    ((u * w : GLV F V) : V →ₗ[F] V) x = (u : V →ₗ[F] V) ((w : V →ₗ[F] V) x) := rfl

@[simp] theorem GLV.one_apply (x : V) : ((1 : GLV F V) : V →ₗ[F] V) x = x := rfl

theorem GLV.ext {u w : GLV F V} (h : ∀ x, (u : V →ₗ[F] V) x = (w : V →ₗ[F] V) x) : u = w :=
  Units.ext (LinearMap.ext h)

theorem GLV.ne_one_iff {u : GLV F V} : u ≠ 1 ↔ ∃ x, (u : V →ₗ[F] V) x ≠ x := by
  refine ⟨fun h => ?_, fun ⟨x, hx⟩ h => hx (by simp [h])⟩
  by_contra hc
  exact h (GLV.ext fun x => by simpa using not_not.1 (not_exists.1 hc x))

/-- The invertible map given by a linear equivalence. -/
def GLV.ofEquiv (e : V ≃ₗ[F] V) : GLV F V :=
  ⟨e.toLinearMap, e.symm.toLinearMap, by ext; simp, by ext; simp⟩

@[simp] theorem GLV.ofEquiv_apply (e : V ≃ₗ[F] V) (x : V) :
    ((GLV.ofEquiv e : GLV F V) : V →ₗ[F] V) x = e x := rfl

@[simp] theorem GLV.ofEquiv_inv_apply (e : V ≃ₗ[F] V) (x : V) :
    (↑(GLV.ofEquiv e)⁻¹ : V →ₗ[F] V) x = e.symm x := rfl

end GLV

section Blocks

variable {V A B B' : Type*} [AddCommGroup V] [Module F V] [AddCommGroup A] [Module F A]
  [AddCommGroup B] [Module F B] [AddCommGroup B'] [Module F B']

/-- `a ⊕ b` along `E : V ≃ A × B`, as a linear map. -/
def blkMap (E : V ≃ₗ[F] A × B) (a : A →ₗ[F] A) (b : B →ₗ[F] B) : V →ₗ[F] V :=
  E.symm.toLinearMap ∘ₗ (a.prodMap b) ∘ₗ E.toLinearMap

@[simp] theorem blkMap_apply (E : V ≃ₗ[F] A × B) (a : A →ₗ[F] A) (b : B →ₗ[F] B) (x : V) :
    blkMap E a b x = E.symm (a (E x).1, b (E x).2) := rfl

/-- `a ⊕ b` along `E : V ≃ A × B`, as a group homomorphism `GL(A) × GL(B) → GL(V)`. -/
def blk (E : V ≃ₗ[F] A × B) : GLV F A × GLV F B →* GLV F V where
  toFun p := ⟨blkMap E p.1 p.2, blkMap E ↑p.1⁻¹ ↑p.2⁻¹, by ext; simp, by ext; simp⟩
  map_one' := by ext; simp
  map_mul' p q := by ext; simp

@[simp] theorem blk_apply (E : V ≃ₗ[F] A × B) (p : GLV F A × GLV F B) (x : V) :
    ((blk E p : GLV F V) : V →ₗ[F] V) x =
      E.symm ((p.1 : A →ₗ[F] A) (E x).1, (p.2 : B →ₗ[F] B) (E x).2) := rfl

/-- Conjugation by a linear equivalence `s : B ≃ B'`. -/
def conjGL (s : B ≃ₗ[F] B') : GLV F B ≃* GLV F B' where
  toFun b := ⟨s.toLinearMap ∘ₗ (b : B →ₗ[F] B) ∘ₗ s.symm.toLinearMap,
    s.toLinearMap ∘ₗ (↑b⁻¹ : B →ₗ[F] B) ∘ₗ s.symm.toLinearMap, by ext; simp, by ext; simp⟩
  invFun b := ⟨s.symm.toLinearMap ∘ₗ (b : B' →ₗ[F] B') ∘ₗ s.toLinearMap,
    s.symm.toLinearMap ∘ₗ (↑b⁻¹ : B' →ₗ[F] B') ∘ₗ s.toLinearMap, by ext; simp, by ext; simp⟩
  left_inv b := by ext; simp
  right_inv b := by ext; simp
  map_mul' b c := by ext; simp

@[simp] theorem conjGL_apply (s : B ≃ₗ[F] B') (b : GLV F B) (x : B') :
    ((conjGL s b : GLV F B') : B' →ₗ[F] B') x = s ((b : B →ₗ[F] B) (s.symm x)) := rfl

theorem conjGL_ne_one {s : B ≃ₗ[F] B'} {b : GLV F B} (hb : b ≠ 1) : conjGL s b ≠ 1 := by
  simpa using hb

/-- `a ⊕ b` only depends on `b` up to conjugation, whatever the splittings. -/
theorem isConj_blk (E : V ≃ₗ[F] A × B) (E' : V ≃ₗ[F] A × B') (s : B ≃ₗ[F] B') (a : GLV F A)
    (b : GLV F B) : IsConj (blk E (a, b)) (blk E' (a, conjGL s b)) := by
  refine isConj_iff.2
    ⟨GLV.ofEquiv (E.trans (((LinearEquiv.refl F A).prodCongr s).trans E'.symm)), ?_⟩
  apply GLV.ext
  intro x
  simp

/-- The restriction of `u` to a subspace that `u` and `u⁻¹` preserve. -/
def restrictGL {V : Type*} [AddCommGroup V] [Module F V] (u : GLV F V) (K : Submodule F V)
    (h : ∀ x ∈ K, (u : V →ₗ[F] V) x ∈ K) (h' : ∀ x ∈ K, (↑u⁻¹ : V →ₗ[F] V) x ∈ K) : GLV F K :=
  ⟨(u : V →ₗ[F] V).restrict h, (↑u⁻¹ : V →ₗ[F] V).restrict h',
    by ext; simp [LinearMap.restrict_apply], by ext; simp [LinearMap.restrict_apply]⟩

@[simp] theorem restrictGL_apply {V : Type*} [AddCommGroup V] [Module F V] (u : GLV F V)
    (K : Submodule F V) (h h') (x : K) :
    (((restrictGL u K h h' : GLV F K) : K →ₗ[F] K) x : V) = (u : V →ₗ[F] V) x := rfl

end Blocks

section Frames

variable {V V' : Type*} [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V'] {m : ℕ}

/-- The common kernel of the covectors `f i`. -/
def frameKer (f : Fin m → Dual F V) : Submodule F V := ⨅ i, LinearMap.ker (f i)

theorem mem_frameKer {f : Fin m → Dual F V} {x : V} : x ∈ frameKer f ↔ ∀ i, f i x = 0 := by
  simp [frameKer, Submodule.mem_iInf]

/-- Vectors `e j` and covectors `f i` with `f i (e j) = δ i j`. -/
def Biorth (e : Fin m → V) (f : Fin m → Dual F V) : Prop :=
  ∀ i j, f i (e j) = if i = j then 1 else 0

variable {e : Fin m → V} {f : Fin m → Dual F V} {e' : Fin m → V'} {f' : Fin m → Dual F V'}

theorem Biorth.apply_sum (h : Biorth e f) (c : Fin m → F) {k : V} (hk : k ∈ frameKer f)
    (i : Fin m) : f i (∑ j, c j • e j + k) = c i := by
  rw [map_add, mem_frameKer.1 hk i, add_zero, map_sum]
  simp [h i]

theorem Biorth.sub_mem (h : Biorth e f) (x : V) : x - ∑ j, f j x • e j ∈ frameKer f := by
  rw [mem_frameKer]
  intro i
  rw [map_sub, map_sum]
  simp [h i]

/-- A frame splits `V` as `F^m × K`, coordinates first. -/
def frameEquiv (h : Biorth e f) : V ≃ₗ[F] (Fin m → F) × frameKer f where
  toFun x := (fun i => f i x, ⟨x - ∑ j, f j x • e j, h.sub_mem x⟩)
  map_add' x y := by
    ext
    · simp
    · simp [add_smul, Finset.sum_add_distrib]
      abel
  map_smul' c x := by
    ext
    · simp
    · simp [smul_sub, Finset.smul_sum, smul_smul]
  invFun p := ∑ j, p.1 j • e j + p.2
  left_inv x := by simp
  right_inv p := by
    have hc : ∀ i, f i (∑ j, p.1 j • e j + p.2) = p.1 i := h.apply_sum p.1 p.2.2
    ext i
    · exact hc i
    · simp [hc]

@[simp] theorem frameEquiv_fst (h : Biorth e f) (x : V) (i : Fin m) :
    (frameEquiv h x).1 i = f i x := rfl

@[simp] theorem frameEquiv_snd (h : Biorth e f) (x : V) :
    ((frameEquiv h x).2 : V) = x - ∑ j, f j x • e j := rfl

@[simp] theorem frameEquiv_symm_apply (h : Biorth e f) (p : (Fin m → F) × frameKer f) :
    (frameEquiv h).symm p = ∑ j, p.1 j • e j + p.2 := rfl

theorem frameEquiv_e (h : Biorth e f) (j : Fin m) :
    frameEquiv h (e j) = (fun i => if i = j then 1 else 0, 0) := by
  have hj : ∀ i, f i (e j) = if i = j then 1 else 0 := fun i => h i j
  ext i
  · simp [hj]
  · simp [hj, ite_smul]

theorem finrank_frameKer [FiniteDimensional F V] (h : Biorth e f) :
    finrank F V = m + finrank F (frameKer f) := by
  rw [(frameEquiv h).finrank_eq, Module.finrank_prod, Module.finrank_fin_fun]

/-- Two frames of the same size, with a matching of their kernels, give an equivalence
carrying the first frame to the second. -/
def frameTransport (h : Biorth e f) (h' : Biorth e' f') (s : frameKer f ≃ₗ[F] frameKer f') :
    V ≃ₗ[F] V' :=
  (frameEquiv h).trans (((LinearEquiv.refl F _).prodCongr s).trans (frameEquiv h').symm)

theorem frameTransport_e (h : Biorth e f) (h' : Biorth e' f') (s : frameKer f ≃ₗ[F] frameKer f')
    (j : Fin m) : frameTransport h h' s (e j) = e' j := by
  simp [frameTransport, frameEquiv_e h j, ite_smul]

theorem frameTransport_f (h : Biorth e f) (h' : Biorth e' f') (s : frameKer f ≃ₗ[F] frameKer f')
    (i : Fin m) (x : V) : f' i (frameTransport h h' s x) = f i x := by
  simp only [frameTransport, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, frameEquiv_symm_apply]
  rw [h'.apply_sum _ (s _).2]
  rfl

/-- `u` is `a ⊕ (u restricted to K)` along a frame, when `u` acts on the frame vectors by the
coordinate map `a`. -/
theorem blk_frameEquiv (h : Biorth e f) (u : GLV F V) (a : GLV F (Fin m → F))
    (hK : ∀ x ∈ frameKer f, (u : V →ₗ[F] V) x ∈ frameKer f)
    (hK' : ∀ x ∈ frameKer f, (↑u⁻¹ : V →ₗ[F] V) x ∈ frameKer f)
    (hu : ∀ c : Fin m → F, ∑ j, c j • (u : V →ₗ[F] V) (e j) =
      ∑ i, (a : (Fin m → F) →ₗ[F] (Fin m → F)) c i • e i) :
    blk (frameEquiv h) (a, restrictGL u _ hK hK') = u := by
  apply GLV.ext
  intro x
  simp only [blk_apply, frameEquiv_symm_apply, restrictGL_apply, frameEquiv_snd, map_sub,
    map_sum, map_smul]
  rw [← hu]
  simp

end Frames


section Blocks2

variable {V A B C : Type*} [AddCommGroup V] [Module F V] [AddCommGroup A] [Module F A]
  [AddCommGroup B] [Module F B] [AddCommGroup C] [Module F C]

theorem blk_eq_one {E : V ≃ₗ[F] A × B} {p : GLV F A × GLV F B} (h : blk E p = 1) : p = 1 := by
  have key : ∀ a b, E.symm ((p.1 : A →ₗ[F] A) a, (p.2 : B →ₗ[F] B) b) = E.symm (a, b) := by
    intro a b
    have := congrArg (fun u : GLV F V => (u : V →ₗ[F] V) (E.symm (a, b))) h
    simpa using this
  have key' : ∀ a b, ((p.1 : A →ₗ[F] A) a, (p.2 : B →ₗ[F] B) b) = (a, b) :=
    fun a b => E.symm.injective (key a b)
  ext x
  · exact congrArg Prod.fst (key' x 0)
  · exact congrArg Prod.snd (key' 0 x)

/-- Exchange the two copies of `A` in `A × (A × C)`. -/
def swap12 (A C : Type*) [AddCommGroup A] [Module F A] [AddCommGroup C] [Module F C] :
    (A × (A × C)) ≃ₗ[F] (A × (A × C)) where
  toFun p := (p.2.1, (p.1, p.2.2))
  invFun p := (p.2.1, (p.1, p.2.2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- `1 ⊕ (a ⊕ 1)` is `a ⊕ 1` for a regrouped splitting. -/
theorem blk_one_blk (E : V ≃ₗ[F] A × B) (E' : B ≃ₗ[F] A × C) (a : GLV F A) :
    blk E (1, blk E' (a, 1)) =
      blk (E.trans (((LinearEquiv.refl F A).prodCongr E').trans (swap12 A C))) (a, 1) := by
  apply GLV.ext
  intro x
  simp [swap12]

end Blocks2

end Vaserstein
