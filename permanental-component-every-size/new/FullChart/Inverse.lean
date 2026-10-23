import FullChart.Elimination
set_option backward.isDefEq.respectTransparency false
namespace UniformFullChart
noncomputable section
open MvPolynomial ComponentChartJacobian

def backwardBasePoly (k : ℕ) : BasePoly k →+* Ambient k :=
  (ambientCoordinates k).comp (rename retain).toRingHom
theorem backwardBasePoly_zero (k : ℕ) (r : Fin 4 ⊕ Unit) :
    backwardBasePoly k (baseEquations k r) = 0 := by
  change ambientCoordinates k (rename retain (baseEquations k r)) = 0
  rw [rename_baseEquation]
  exact ambient_generator_zero k _
def backwardBaseQuot (k : ℕ) : BaseQuot k →+* Ambient k :=
  Ideal.Quotient.lift _ (backwardBasePoly k) (by
    change baseIdeal k ≤ RingHom.ker (backwardBasePoly k)
    apply Ideal.span_le.mpr
    rintro _ ⟨r,rfl⟩
    exact backwardBasePoly_zero k r)
theorem backwardBasePivot_unit (k : ℕ) : IsUnit (backwardBaseQuot k (basePivot k)) := by
  simpa [backwardBaseQuot,basePivot,backwardBasePoly,retain,ambientEntry,ambientCoordinates,ambientPivot] using
    IsLocalization.Away.algebraMap_isUnit (S := Ambient k) (ambientPivot k)
def backwardBase (k : ℕ) : Base k →+* Ambient k :=
  IsLocalization.Away.lift (basePivot k) (backwardBasePivot_unit k)
def backward (k : ℕ) : Target k →+* Ambient k :=
  eval₂Hom (backwardBase k) (fun j => ambientEntry k (vVar (0,j)))

@[simp] theorem backwardBase_entry (k : ℕ) (ij : Retained k) :
    backwardBase k (baseEntry k ij) = ambientEntry k (retain ij) := by
  simp [backwardBase,baseEntry,baseCoordinates,backwardBaseQuot,
    backwardBasePoly,ambientEntry]
@[simp] theorem backward_C (k : ℕ) (a : Base k) :
    backward k (C a) = backwardBase k a := by simp [backward]
@[simp] theorem backward_X (k : ℕ) (j : Fin k) :
    backward k (X j) = ambientEntry k (vVar (0,j)) := by simp [backward]
@[simp] theorem forward_entry (k : ℕ) (x : Variables k) :
    forward k (ambientEntry k x) = forwardEntry k x := by
  simp [forward,ambientEntry,ambientCoordinates,forwardQuot]
theorem backwardBase_unit (k : ℕ) :
    Units.map (backwardBase k).toMonoidHom (baseUnit k) = ambientUnit k := by
  apply Units.ext
  change backwardBase k (baseUnit k : Base k) = (ambientUnit k : Ambient k)
  rw [baseUnit_value,backwardBase_entry,ambientUnit_value]
  rfl
theorem backwardBase_invUnit (k : ℕ) :
    backwardBase k (↑(baseUnit k)⁻¹) = (↑(ambientUnit k)⁻¹ : Ambient k) := by
  have h := congrArg (fun u : (Ambient k)ˣ => (u : Ambient k))
    (show Units.map (backwardBase k).toMonoidHom ((baseUnit k)⁻¹) = (ambientUnit k)⁻¹ by
      rw [map_inv,backwardBase_unit])
  exact h

theorem ambient_l_zero (k : ℕ) (a : LIndex k) : ambientEntry k (lVar a) = 0 :=
  ambient_generator_zero k (.inr (.inr (.inl a)))
theorem ambient_proportionality (k : ℕ) (i : Fin 3) (j : Fin k) :
    ambientEntry k (bVar (0,3)) * ambientEntry k (vVar (i,j)) =
      ambientEntry k (bVar (i,3)) * ambientEntry k (vVar (0,j)) := by
  refine Fin.cases ?_ (fun a => ?_) i
  · rfl
  · have h := ambient_generator_zero k (.inr (.inr (.inr (a,j))))
    simpa [generator,proportionality,ambientEntry,map_sub,map_mul,sub_eq_zero] using h

theorem ambient_v_solved (k : ℕ) (i : Fin 3) (j : Fin k) :
    ambientEntry k (vVar (i,j)) =
      ambientEntry k (bVar (i,3)) * (↑(ambientUnit k)⁻¹ : Ambient k) *
        ambientEntry k (vVar (0,j)) := by
  apply (ambientUnit k).isUnit.mul_left_cancel
  rw [ambientUnit_value,ambient_proportionality]
  rw [← ambientUnit_value]
  simp only [←mul_assoc]
  have hc := (ambientUnit k).mul_inv
  calc
    _ = ((ambientUnit k : Ambient k) * (↑(ambientUnit k)⁻¹ : Ambient k)) *
      ambientEntry k (bVar (i,3)) * ambientEntry k (vVar (0,j)) := by simp
    _ = _ := by ring

theorem backward_forward_entry (k : ℕ) (x : Variables k) :
    backward k (forward k (ambientEntry k x)) = ambientEntry k x := by
  rw [forward_entry]
  rcases x with ij | (ij | (a | ij))
  · simp [forwardEntry,retain,bVar]
  · simp [forwardEntry,retain,wVar]
  · simpa only [forwardEntry,map_zero,lVar] using (ambient_l_zero k a).symm
  · simp only [forwardEntry,map_mul,backward_C,backward_X,backwardBase_entry,backwardBase_invUnit]
    exact (ambient_v_solved k ij.1 ij.2).symm

#print axioms backward_forward_entry
end
end UniformFullChart
