import FullChart.Equivalence
set_option backward.isDefEq.respectTransparency false
namespace UniformFullChart
noncomputable section
open MvPolynomial ComponentChartJacobian
def seedQuotient (k : ℕ) : AmbientQuot k →+* ℂ :=
  Ideal.Quotient.lift _ (eval (seed k)) (by
    change ambientIdeal k ≤ RingHom.ker (eval (seed k))
    apply Ideal.span_le.mpr
    rintro _ ⟨r,rfl⟩
    exact generator_vanishes_at_seed k r)
theorem seedPivot_eq (k : ℕ) : seedQuotient k (ambientPivot k) = 1 := by
  simp [seedQuotient,ambientPivot,seed,bVar,ComponentUpperSeed.B]
def ambientSeed (k : ℕ) : Ambient k →+* ℂ :=
  IsLocalization.Away.lift (ambientPivot k) (by rw [seedPivot_eq]; exact isUnit_one)
@[simp] theorem ambientSeed_entry (k : ℕ) (x : Variables k) :
    ambientSeed k (ambientEntry k x) = seed k x := by
  simp [ambientSeed,ambientEntry,ambientCoordinates,seedQuotient]
def coefficientSeed (k : ℕ) : Base k →+* ℂ :=
  (ambientSeed k).comp (backwardBase k)
@[simp] theorem coefficientSeed_entry (k : ℕ) (x : Retained k) :
    coefficientSeed k (baseEntry k x) = seed k (retain x) := by
  simp [coefficientSeed]
def targetSeed (k : ℕ) : Target k →+* ℂ :=
  eval₂Hom (coefficientSeed k) (fun _ => 2)
theorem seed_intertwines (k : ℕ) :
    (ambientSeed k).comp (backward k) = targetSeed k := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [targetSeed,coefficientSeed]
  · intro j
    simp [targetSeed,seed,vVar,ComponentUpperSeed.v,ComponentUpperSeed.B]
theorem seed_forward (k : ℕ) :
    (targetSeed k).comp (forward k) = ambientSeed k := by
  rw [← seed_intertwines, RingHom.comp_assoc,backward_forward]
  rfl

def ambientSeedAlg (k : ℕ) : Ambient k →ₐ[ℂ] ℂ :=
  { ambientSeed k with
    commutes' := by
      intro z
      change ambientSeed k (algebraMap (AmbientQuot k) (Ambient k)
        (Ideal.Quotient.mk (ambientIdeal k) (C z))) = z
      simp [ambientSeed,seedQuotient] }

def coefficientSeedAlg (k : ℕ) : Base k →ₐ[ℂ] ℂ :=
  { coefficientSeed k with
    commutes' := by
      intro z
      change ambientSeed k (backwardBase k (algebraMap (BaseQuot k) (Base k)
        (Ideal.Quotient.mk (baseIdeal k) (C z)))) = z
      simp [backwardBase,backwardBaseQuot,backwardBasePoly,ambientCoordinates,
        ambientSeed,seedQuotient] }

instance ambient_nontrivial (k : ℕ) : Nontrivial (Ambient k) :=
  (ambientSeed k).domain_nontrivial

#print axioms seed_forward
end
end UniformFullChart
