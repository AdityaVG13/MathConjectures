import ChartJacobian.ChartIdealBridge
import Mathlib.RingTheory.Localization.Away.Basic
set_option backward.isDefEq.respectTransparency false
namespace UniformFullChart
noncomputable section
open MvPolynomial ComponentChartJacobian

abbrev Retained (k : ℕ) := BIndex ⊕ WIndex k
abbrev BasePoly (k : ℕ) := MvPolynomial (Retained k) ℂ
def retain {k : ℕ} : Retained k → Variables k
  | .inl ij => bVar ij
  | .inr ij => wVar ij
def baseEquations (k : ℕ) : Fin 4 ⊕ Unit → BasePoly k
  | .inl c => rename Sum.inl ((ComponentUpperSeed.genericB.submatrix id c.succAbove).permanent)
  | .inr _ => rename Sum.inr (genericW k).permanent
def baseIdeal (k : ℕ) : Ideal (BasePoly k) := Ideal.span (Set.range (baseEquations k))
abbrev BaseQuot (k : ℕ) := BasePoly k ⧸ baseIdeal k
def basePivot (k : ℕ) : BaseQuot k := Ideal.Quotient.mk (baseIdeal k) (X (.inl (0,3)))
abbrev Base (k : ℕ) := Localization.Away (basePivot k)
def baseCoordinates (k : ℕ) : BasePoly k →+* Base k :=
  (algebraMap (BaseQuot k) (Base k)).comp (Ideal.Quotient.mk (baseIdeal k))
def baseEntry (k : ℕ) (ij : Retained k) : Base k := baseCoordinates k (X ij)
def baseUnit (k : ℕ) : (Base k)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := Base k) (basePivot k)).unit
theorem baseUnit_value (k : ℕ) : (baseUnit k : Base k) = baseEntry k (.inl (0,3)) :=
  (IsLocalization.Away.algebraMap_isUnit (S := Base k) (basePivot k)).unit_spec

def ambientIdeal (k : ℕ) : Ideal (P k) := Ideal.span (Set.range (generator k))
abbrev AmbientQuot (k : ℕ) := P k ⧸ ambientIdeal k
def ambientPivot (k : ℕ) : AmbientQuot k :=
  Ideal.Quotient.mk (ambientIdeal k) (X (bVar (0,3)))
abbrev Ambient (k : ℕ) := Localization.Away (ambientPivot k)
def ambientCoordinates (k : ℕ) : P k →+* Ambient k :=
  (algebraMap (AmbientQuot k) (Ambient k)).comp (Ideal.Quotient.mk (ambientIdeal k))
def ambientEntry (k : ℕ) (x : Variables k) : Ambient k := ambientCoordinates k (X x)
def ambientUnit (k : ℕ) : (Ambient k)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := Ambient k) (ambientPivot k)).unit
theorem ambientUnit_value (k : ℕ) : (ambientUnit k : Ambient k) = ambientEntry k (bVar (0,3)) :=
  (IsLocalization.Away.algebraMap_isUnit (S := Ambient k) (ambientPivot k)).unit_spec
abbrev Target (k : ℕ) := MvPolynomial (Fin k) (Base k)

theorem ambient_generator_zero (k : ℕ) (r : Generators k) :
    ambientCoordinates k (generator k r) = 0 := by
  change algebraMap (AmbientQuot k) (Ambient k) (Ideal.Quotient.mk (ambientIdeal k) (generator k r)) = 0
  have hm : generator k r ∈ ambientIdeal k := Ideal.subset_span (Set.mem_range_self r)
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm,map_zero]
theorem base_equation_zero (k : ℕ) (r : Fin 4 ⊕ Unit) :
    baseCoordinates k (baseEquations k r) = 0 := by
  change algebraMap (BaseQuot k) (Base k) (Ideal.Quotient.mk (baseIdeal k) (baseEquations k r)) = 0
  have hm : baseEquations k r ∈ baseIdeal k := Ideal.subset_span (Set.mem_range_self r)
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm,map_zero]

def forwardEntry (k : ℕ) : Variables k → Target k
  | .inl ij => C (baseEntry k (.inl ij))
  | .inr (.inl ij) => C (baseEntry k (.inr ij))
  | .inr (.inr (.inl _)) => 0
  | .inr (.inr (.inr ij)) =>
      C (baseEntry k (.inl (ij.1,3))) * C (↑(baseUnit k)⁻¹) * X ij.2
def forwardPoly (k : ℕ) : P k →+* Target k :=
  eval₂Hom ((C : Base k →+* Target k).comp ((baseCoordinates k).comp C)) (forwardEntry k)

@[simp] theorem forwardPoly_X (k : ℕ) (x : Variables k) :
    forwardPoly k (X x) = forwardEntry k x := by simp [forwardPoly]
@[simp] theorem forwardPoly_C (k : ℕ) (z : ℂ) :
    forwardPoly k (C z) = C (baseCoordinates k (C z)) := by simp [forwardPoly]
theorem forward_retained (k : ℕ) (p : BasePoly k) :
    forwardPoly k (rename retain p) = C (baseCoordinates k p) := by
  induction p using MvPolynomial.induction_on with
  | C z => simp [forwardPoly,baseCoordinates]
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    cases i <;> simp [hp,forwardEntry,retain,bVar,wVar,baseEntry]

theorem rename_baseEquation (k : ℕ) (r : Fin 4 ⊕ Unit) :
    rename retain (baseEquations k r) =
      generator k (Sum.elim Sum.inl (fun _ => .inr (.inl ())) r) := by
  cases r <;> simp [baseEquations,generator,upperPolynomial,lowerPolynomial,
    rename_rename,Function.comp_def,retain]

theorem forward_generator (k : ℕ) (r : Generators k) :
    forwardPoly k (generator k r) = 0 := by
  rcases r with c | (_ | (ac | ij))
  · have he := rename_baseEquation k (.inl c)
    simp only [Sum.elim_inl] at he
    rw [← he,forward_retained,base_equation_zero,map_zero]
  · have he := rename_baseEquation k (.inr ())
    simp only [Sum.elim_inr] at he
    change forwardPoly k (generator k (.inr (.inl ()))) = 0
    rw [← he,forward_retained,base_equation_zero,map_zero]
  · simp [generator,forwardPoly,forwardEntry,lVar]
  · simp only [generator,proportionality,map_sub,map_mul,forwardPoly_X]
    simp only [forwardEntry,bVar,vVar]
    ring

def forwardQuot (k : ℕ) : AmbientQuot k →+* Target k :=
  Ideal.Quotient.lift _ (forwardPoly k) (by
    change ambientIdeal k ≤ RingHom.ker (forwardPoly k)
    apply Ideal.span_le.mpr
    rintro _ ⟨r,rfl⟩
    exact forward_generator k r)

theorem forwardPivot_unit (k : ℕ) : IsUnit (forwardQuot k (ambientPivot k)) := by
  simp only [forwardQuot,ambientPivot,Ideal.Quotient.lift_mk,forwardPoly_X,forwardEntry,bVar]
  rw [← baseUnit_value]
  exact (baseUnit k).isUnit.map C

def forward (k : ℕ) : Ambient k →+* Target k :=
  IsLocalization.Away.lift (ambientPivot k) (forwardPivot_unit k)

#print axioms forward
end
end UniformFullChart
