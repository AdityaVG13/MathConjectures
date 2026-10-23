import GeometryBridge.UpperQuadraticChart
import ExceptionalIntrinsicElimination

namespace UniformNormalizedUpper
noncomputable section
open UniformUpperQuadratic
open ExceptionalIntrinsic

abbrev Coordinates := MvPolynomial (Fin 6) ℂ

def vars : Fin 6 → Coordinates := MvPolynomial.X

def constraints : Fin 4 → Coordinates :=
  ![P (vars 0) (vars 1) (vars 5) (vars 2) (vars 3) (vars 4),
    C0 (vars 0) (vars 1) (vars 5) (vars 2) (vars 3) (vars 4),
    C1 (vars 0) (vars 1) (vars 5) (vars 2) (vars 3) (vars 4),
    C2 (vars 0) (vars 1) (vars 5) (vars 2) (vars 3) (vars 4)]
/-- The actual normalized 3 by 4 matrix, with first row and first column equal to one. -/
def normalizedMatrix : Matrix (Fin 3) (Fin 4) Coordinates :=
  !![1,1,1,1; 1,vars 2,vars 3,vars 0; 1,vars 1,vars 4,vars 5]

def actualCofactor (k : Fin 4) : Coordinates :=
  (normalizedMatrix.submatrix id k.succAbove).permanent

theorem actualCofactor_eq (k : Fin 4) :
    actualCofactor k = ![constraints 1, constraints 2, constraints 3, constraints 0] k := by
  fin_cases k <;> rw [actualCofactor, PrimitiveFamily.expand3] <;>
    norm_num [Fin.sum_univ_succ, Fin.prod_univ_succ, PrimitiveFamily.enumerate3,
      PrimitiveFamily.q0, PrimitiveFamily.q1, PrimitiveFamily.q2, PrimitiveFamily.q3,
      PrimitiveFamily.q4, PrimitiveFamily.q5, normalizedMatrix, Matrix.submatrix, Fin.succAbove, constraints, P, C0, C1, C2] <;> ring

def ideal : Ideal Coordinates := Ideal.span (Set.range constraints)
theorem ideal_eq_actualCofactors : ideal = Ideal.span (Set.range actualCofactor) := by
  unfold ideal
  congr 1
  ext p
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact ⟨3, by simp [actualCofactor_eq]⟩
    · exact ⟨0, by simp [actualCofactor_eq]⟩
    · exact ⟨1, by simp [actualCofactor_eq]⟩
    · exact ⟨2, by simp [actualCofactor_eq]⟩
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact ⟨1, by simp [actualCofactor_eq]⟩
    · exact ⟨2, by simp [actualCofactor_eq]⟩
    · exact ⟨3, by simp [actualCofactor_eq]⟩
    · exact ⟨0, by simp [actualCofactor_eq]⟩

abbrev Quot := Coordinates ⧸ ideal

def qDenom : Quot := Ideal.Quotient.mk ideal (denom (vars 0) (vars 1))
abbrev Normalized := Localization.Away qDenom

def coordinates : Coordinates →+* Normalized :=
  (algebraMap Quot Normalized).comp (Ideal.Quotient.mk ideal)
def v (i : Fin 6) : Normalized := coordinates (vars i)

theorem constraints_zero (i : Fin 4) : coordinates (constraints i) = 0 := by
  change algebraMap Quot Normalized (Ideal.Quotient.mk ideal (constraints i)) = 0
  have hm : constraints i ∈ ideal := Ideal.subset_span (Set.mem_range_self i)
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm, map_zero]

theorem four_zero :
    P (v 0) (v 1) (v 5) (v 2) (v 3) (v 4) = 0 ∧
    C0 (v 0) (v 1) (v 5) (v 2) (v 3) (v 4) = 0 ∧
    C1 (v 0) (v 1) (v 5) (v 2) (v 3) (v 4) = 0 ∧
    C2 (v 0) (v 1) (v 5) (v 2) (v 3) (v 4) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [constraints, P, v] using constraints_zero 0
  · simpa [constraints, C0, v] using constraints_zero 1
  · simpa [constraints, C1, v] using constraints_zero 2
  · simpa [constraints, C2, v] using constraints_zero 3

theorem two_unit : IsUnit (2 : Normalized) := by
  simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℂ) ≠ 0)).map
    (algebraMap ℂ Normalized)

theorem i_zero : I (v 0) (v 1) (v 5) (v 4) = 0 := by
  apply two_unit.mul_left_cancel
  simpa [four_zero.1, four_zero.2.1, four_zero.2.2.1, four_zero.2.2.2] using
    i_identity (v 0) (v 1) (v 5) (v 2) (v 3) (v 4)

theorem relation_zero : ExceptionalCriticalFamily.relation (v 0) (v 1) (v 5) = 0 := by
  have hr := relation_identity (v 0) (v 1) (v 5) (v 2) (v 3) (v 4)
  simp only [four_zero.1, four_zero.2.2.1, four_zero.2.2.2, i_zero,
    mul_zero, zero_mul, zero_add, add_zero, sub_zero, zero_sub] at hr
  apply two_unit.mul_left_cancel
  simpa using neg_eq_zero.mp hr

theorem quadratic_zero : alpha (v 0) (v 1)*(v 5)^2 + beta (v 0) (v 1)*(v 5) +
    gamma (v 0) (v 1) = 0 := by
  rw [← relation_expansion]
  exact relation_zero

theorem denom_unit : IsUnit (denom (v 0) (v 1)) := by
  have hu := IsLocalization.Away.algebraMap_isUnit (S := Normalized) qDenom
  simpa [qDenom, v, coordinates, denom, rest, disc, normPlus, normMinus, alpha, beta, gamma, map_ofNat] using hu

theorem alpha_unit : IsUnit (alpha (v 0) (v 1)) :=
  isUnit_of_mul_isUnit_left denom_unit

theorem plus_unit : IsUnit (v 5 + 1) := by
  have hn : IsUnit (normPlus (v 0) (v 1)) :=
    isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left
      (isUnit_of_mul_isUnit_right denom_unit))
  have hu : IsUnit (alpha (v 0) (v 1)*(-1)^2 + beta (v 0) (v 1)*(-1) + gamma (v 0) (v 1)) := by
    simpa [normPlus, sub_eq_add_neg] using hn
  simpa using quadratic_root_shift_isUnit _ _ _ (v 5) (-1) quadratic_zero hu

theorem minus_unit : IsUnit (v 5 - v 0) := by
  have hn : IsUnit (normMinus (v 0) (v 1)) :=
    isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right denom_unit)
  exact quadratic_root_shift_isUnit _ _ _ (v 5) (v 0) quadratic_zero hn

def paramsMap : Parameters →+* Normalized :=
  MvPolynomial.eval₂Hom (algebraMap ℂ Normalized) ![v 0, v 1]

@[simp] theorem paramsMap_d : paramsMap d = v 0 := by simp [paramsMap, d]
@[simp] theorem paramsMap_h : paramsMap h = v 1 := by simp [paramsMap, h]

theorem paramsMap_denom_unit : IsUnit (paramsMap (denom d h)) := by
  simpa [denom, rest, disc, normPlus, normMinus, alpha, beta, gamma, map_ofNat] using denom_unit

def baseToNormalized : Base →+* Normalized :=
  IsLocalization.Away.lift (denom d h) paramsMap_denom_unit

@[simp] theorem baseToNormalized_map (a : Parameters) :
    baseToNormalized (algebraMap Parameters Base a) = paramsMap a :=
  IsLocalization.Away.lift_eq _ _ a

theorem normalized_monic_zero : (UniformUpperQuadratic.equation).eval₂ baseToNormalized (v 5) = 0 := by
  simp only [UniformUpperQuadratic.equation, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, map_one, one_mul]
  have hb := congrArg baseToNormalized alpha_mul_b
  have hc := congrArg baseToNormalized alpha_mul_c
  simp only [map_mul, baseToNormalized_map] at hb hc
  simp only [alpha, beta, gamma, map_add, map_sub, map_mul, map_pow, map_neg,
    map_one, paramsMap_d, paramsMap_h] at hb hc
  change alpha (v 0) (v 1) * baseToNormalized b = beta (v 0) (v 1) at hb
  change alpha (v 0) (v 1) * baseToNormalized c = gamma (v 0) (v 1) at hc
  apply alpha_unit.mul_left_cancel
  rw [mul_zero, mul_add, mul_add, ← mul_assoc, hb, hc]
  exact quadratic_zero

def toNormalized : Chart →+* Normalized :=
  AdjoinRoot.lift baseToNormalized (v 5) normalized_monic_zero

@[simp] theorem toNormalized_j : toNormalized j = v 5 :=
  AdjoinRoot.lift_root _

@[simp] theorem toNormalized_base (a : Base) :
    toNormalized (algebraMap Base Chart a) = baseToNormalized a :=
  AdjoinRoot.lift_of _

def solve {T : Type*} [CommRing T] (a : T) (ha : IsUnit a) (rhs : T) : T :=
  rhs * ↑ha.unit⁻¹

theorem mul_solve {T : Type*} [CommRing T] (a : T) (ha : IsUnit a) (rhs : T) :
    a * solve a ha rhs = rhs := by
  dsimp [solve]
  calc
    _ = rhs * (a * ↑ha.unit⁻¹) := by ring
    _ = rhs := by rw [ha.mul_val_inv, mul_one]

def cd : Chart := parameterMap d
def ch : Chart := parameterMap h
def ce : Chart := solve (j+1) root_add_one_unit
  (ExceptionalCriticalFamily.eNumerator cd ch j)
def ci : Chart := solve (j-cd) root_sub_d_unit (-(j-1)*(j+cd)) - ch
def cf : Chart := solve ((j+1)*(j-cd)) (root_add_one_unit.mul root_sub_d_unit)
  (ExceptionalCriticalFamily.fNumerator cd ch j)

theorem chart_relation_zero : ExceptionalCriticalFamily.relation cd ch j = 0 := by
  rw [ExceptionalCriticalFamily.relation, relation_expansion]
  simpa [cd, ch, alpha, beta, gamma] using original_root_equation

theorem chart_solved : E cd ch j ce = 0 ∧ I cd ch j ci = 0 ∧ F cd ch j cf = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact sub_eq_zero.mpr (mul_solve _ _ _)
  · dsimp [I, ci, cd]
    rw [sub_add_cancel, mul_solve]
    ring
  · exact sub_eq_zero.mpr (mul_solve _ _ _)

theorem chart_four_zero : P cd ch j ce cf ci = 0 ∧ C0 cd ch j ce cf ci = 0 ∧
    C1 cd ch j ce cf ci = 0 ∧ C2 cd ch j ce cf ci = 0 := by
  apply (constraints_iff cd ch j ce cf ci _ root_add_one_unit root_sub_d_unit).mpr
  · exact ⟨chart_solved.1, chart_solved.2.1, chart_solved.2.2, chart_relation_zero⟩
  · simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℂ) ≠ 0)).map (algebraMap ℂ Chart)

def chartVars : Fin 6 → Chart := ![cd,ch,ce,cf,ci,j]
def toChartPolynomial : Coordinates →+* Chart :=
  MvPolynomial.eval₂Hom (algebraMap ℂ Chart) chartVars

@[simp] theorem toChartPolynomial_var (i : Fin 6) :
    toChartPolynomial (vars i) = chartVars i := by simp [toChartPolynomial, vars]

theorem toChartPolynomial_constraints (i : Fin 4) : toChartPolynomial (constraints i) = 0 := by
  fin_cases i
  · simpa [constraints, P, chartVars] using chart_four_zero.1
  · simpa [constraints, C0, chartVars] using chart_four_zero.2.1
  · simpa [constraints, C1, chartVars] using chart_four_zero.2.2.1
  · simpa [constraints, C2, chartVars] using chart_four_zero.2.2.2

def toChartQuot : Quot →+* Chart :=
  Ideal.Quotient.lift ideal toChartPolynomial (by
    change ideal ≤ RingHom.ker toChartPolynomial
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact toChartPolynomial_constraints i)

@[simp] theorem toChartQuot_mk (p : Coordinates) :
    toChartQuot (Ideal.Quotient.mk ideal p) = toChartPolynomial p := rfl

theorem chart_denom_unit : IsUnit (denom cd ch) := by
  have hu := IsLocalization.Away.algebraMap_isUnit (S := Base) (denom d h)
  have hu' := hu.map (algebraMap Base Chart)
  simpa [cd, ch, parameterMap, denom, rest, disc, normPlus, normMinus, alpha, beta, gamma,
    map_ofNat] using hu'

theorem toChartQuot_denom_unit : IsUnit (toChartQuot qDenom) := by
  simpa [qDenom, denom, rest, disc, normPlus, normMinus, alpha, beta, gamma, chartVars,
    map_ofNat] using chart_denom_unit

def toChart : Normalized →+* Chart :=
  IsLocalization.Away.lift qDenom toChartQuot_denom_unit

@[simp] theorem toChart_map (a : Quot) :
    toChart (algebraMap Quot Normalized a) = toChartQuot a :=
  IsLocalization.Away.lift_eq _ _ a

@[simp] theorem toChart_v (i : Fin 6) : toChart (v i) = chartVars i := by
  simp [v, coordinates]

@[simp] theorem toNormalized_cd : toNormalized cd = v 0 := by
  change toNormalized (algebraMap Base Chart (algebraMap Parameters Base d)) = v 0
  rw [toNormalized_base, baseToNormalized_map, paramsMap_d]
@[simp] theorem toNormalized_ch : toNormalized ch = v 1 := by
  change toNormalized (algebraMap Base Chart (algebraMap Parameters Base h)) = v 1
  rw [toNormalized_base, baseToNormalized_map, paramsMap_h]

theorem solved_unique {T : Type*} [CommRing T] (d h j e1 f1 i1 e2 f2 i2 : T)
    (hp : IsUnit (j+1)) (hm : IsUnit (j-d))
    (h1 : E d h j e1 = 0 ∧ I d h j i1 = 0 ∧ F d h j f1 = 0)
    (h2 : E d h j e2 = 0 ∧ I d h j i2 = 0 ∧ F d h j f2 = 0) :
    e1 = e2 ∧ f1 = f2 ∧ i1 = i2 := by
  refine ⟨?_, ?_, ?_⟩
  · apply hp.mul_left_cancel
    exact (sub_eq_zero.mp h1.1).trans (sub_eq_zero.mp h2.1).symm
  · apply (hp.mul hm).mul_left_cancel
    exact (sub_eq_zero.mp h1.2.2).trans (sub_eq_zero.mp h2.2.2).symm
  · have he : (j-d)*(i1+h) = (j-d)*(i2+h) :=
      add_right_cancel (h1.2.1.trans h2.2.1.symm)
    exact add_right_cancel (hm.mul_left_cancel he)

theorem normalized_solved : E (v 0) (v 1) (v 5) (v 2) = 0 ∧
    I (v 0) (v 1) (v 5) (v 4) = 0 ∧ F (v 0) (v 1) (v 5) (v 3) = 0 := by
  have he := (constraints_iff _ _ _ _ _ _ two_unit plus_unit minus_unit).mp four_zero
  exact ⟨he.1, he.2.1, he.2.2.1⟩

theorem toNormalized_solved : toNormalized ce = v 2 ∧ toNormalized cf = v 3 ∧
    toNormalized ci = v 4 := by
  apply solved_unique (v 0) (v 1) (v 5) _ _ _ _ _ _ plus_unit minus_unit _ normalized_solved
  have he := congrArg toNormalized chart_solved.1
  have hi := congrArg toNormalized chart_solved.2.1
  have hf := congrArg toNormalized chart_solved.2.2
  simp only [E, I, F, ExceptionalCriticalFamily.eNumerator,
    ExceptionalCriticalFamily.fNumerator, ExceptionalCriticalFamily.denominator,
    map_sub, map_add, map_mul, map_neg, map_zero, map_one,
    toNormalized_cd, toNormalized_ch, toNormalized_j] at he hi hf ⊢
  exact ⟨he, hi, hf⟩

@[simp] theorem toNormalized_chartVars (i : Fin 6) : toNormalized (chartVars i) = v i := by
  fin_cases i
  · exact toNormalized_cd
  · exact toNormalized_ch
  · exact toNormalized_solved.1
  · exact toNormalized_solved.2.1
  · exact toNormalized_solved.2.2
  · exact toNormalized_j

@[simp] theorem toNormalized_scalar (z : ℂ) :
    toNormalized (algebraMap ℂ Chart z) = algebraMap ℂ Normalized z := by
  change toNormalized (algebraMap Base Chart
    (algebraMap Parameters Base (MvPolynomial.C z))) = _
  rw [toNormalized_base, baseToNormalized_map]
  simp [paramsMap]

@[simp] theorem toChart_scalar (z : ℂ) :
    toChart (algebraMap ℂ Normalized z) = algebraMap ℂ Chart z := by
  change toChart (algebraMap Quot Normalized (Ideal.Quotient.mk ideal (MvPolynomial.C z))) = _
  rw [toChart_map, toChartQuot_mk]
  simp [toChartPolynomial]

theorem toNormalized_comp_toChart : toNormalized.comp toChart = RingHom.id Normalized := by
  apply IsLocalization.ringHom_ext (Submonoid.powers qDenom)
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro z
    change toNormalized (toChart (algebraMap ℂ Normalized z)) = algebraMap ℂ Normalized z
    rw [toChart_scalar, toNormalized_scalar]
  · intro i
    change toNormalized (toChart (v i)) = v i
    rw [toChart_v, toNormalized_chartVars]

theorem toChart_comp_toNormalized : toChart.comp toNormalized = RingHom.id Chart := by
  apply AdjoinRoot.ringHom_ext
  · apply IsLocalization.ringHom_ext (Submonoid.powers (denom d h))
    apply MvPolynomial.ringHom_ext
    · intro z
      change toChart (toNormalized (algebraMap ℂ Chart z)) = algebraMap ℂ Chart z
      rw [toNormalized_scalar, toChart_scalar]
    · intro i
      fin_cases i
      · change toChart (toNormalized cd) = cd
        rw [toNormalized_cd, toChart_v]
        rfl
      · change toChart (toNormalized ch) = ch
        rw [toNormalized_ch, toChart_v]
        rfl
  · change toChart (toNormalized j) = j
    rw [toNormalized_j, toChart_v]
    rfl

/-- The actual four-equation normalized upper permanent chart is the explicit
finite free quadratic root algebra after inverting the stated base polynomial. -/
def normalizedEquiv : Chart ≃+* Normalized where
  toFun := toNormalized
  invFun := toChart
  left_inv := fun x => RingHom.congr_fun toChart_comp_toNormalized x
  right_inv := fun x => RingHom.congr_fun toNormalized_comp_toChart x
  map_mul' := toNormalized.map_mul
  map_add' := toNormalized.map_add

def normalizedAlgEquiv : Chart ≃ₐ[ℂ] Normalized :=
  { normalizedEquiv with commutes' := toNormalized_scalar }

#print axioms normalizedAlgEquiv
#print axioms ideal_eq_actualCofactors
#print axioms normalizedEquiv
#print axioms toChart
#print axioms toNormalized
#print axioms quadratic_zero
end
end UniformNormalizedUpper
