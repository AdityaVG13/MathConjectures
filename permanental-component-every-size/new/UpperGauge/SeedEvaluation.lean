import UpperGauge.ActualChart
import UpperSeed.UpperSeed
set_option backward.isDefEq.respectTransparency false
namespace UniformUpperGauge
noncomputable section
open MvPolynomial
def seedPolynomial : P →+* ℂ := eval (fun ij => ComponentUpperSeed.B ij.1 ij.2)
theorem seed_delta : seedPolynomial delta = 1 := by
  simp [seedPolynomial,delta,Fintype.prod_sum_type,pivot,ComponentUpperSeed.B,Fin.prod_univ_succ]
def seedLocalization : A →+* ℂ :=
  IsLocalization.Away.lift delta (by rw [seed_delta]; exact isUnit_one)
@[simp] theorem seed_matrix (i : Fin 3) (j : Fin 4) :
    seedLocalization (matrix i j) = ComponentUpperSeed.B i j := by
  simp [seedLocalization,matrix,seedPolynomial]
@[simp] theorem seed_units (p : Pivot) : seedLocalization (units p : A) = 1 := by
  rw [units_value,seed_matrix]
  cases p with
  | inl j => fin_cases j <;> norm_num [pivot,ComponentUpperSeed.B]
  | inr i => fin_cases i <;> norm_num [pivot,ComponentUpperSeed.B]
@[simp] theorem seed_scale (i : Fin 3) (j : Fin 4) :
    seedLocalization (scale i j : A) = 1 := by
  have hu : ∀ p, Units.map seedLocalization.toMonoidHom (units p) = 1 := by
    intro p
    apply Units.ext
    exact seed_units p
  have hs : Units.map seedLocalization.toMonoidHom (scale i j) = 1 := by
    refine Fin.cases ?_ (fun r => ?_) i <;>
      simp only [scale,rho,gamma,Fin.cases_zero,Fin.cases_succ,map_mul,map_inv,map_one]
    · simp only [hu,one_mul,inv_one]
    · simp only [hu,one_mul,inv_one]
  exact congrArg (fun u : ℂˣ => (u : ℂ)) hs
@[simp] theorem seed_scale_inv (i : Fin 3) (j : Fin 4) :
    seedLocalization (↑(scale i j)⁻¹ : A) = 1 := by
  have h := congrArg seedLocalization (scale i j).mul_inv
  simpa only [map_mul,seed_scale,map_one,one_mul] using h
@[simp] theorem seed_forwardImage (x : Index) :
    seedLocalization (forwardImage x) = seedPolynomial (X x) := by
  simp [forwardImage,apply_ite,seedPolynomial]
theorem seed_forwardMap : seedLocalization.comp forwardMap = seedLocalization := by
  apply IsLocalization.ringHom_ext (Submonoid.powers delta)
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [forwardMap,forwardPoly,seedLocalization,seedPolynomial]
  · intro ij
    change seedLocalization (forwardMap (matrix ij.1 ij.2)) = seedLocalization (matrix ij.1 ij.2)
    rw [forwardMap_matrix,seed_forwardImage,seed_matrix]
    simp [seedPolynomial]
theorem seed_cofactor (c : Fin 4) : seedLocalization (cofactor matrix c) = 0 := by
  have h := ComponentUpperSeed.maximal_permanents_zero c
  simpa [cofactor,ComponentUpperSeed.maximalPermanent,Matrix.permanent,
    Matrix.submatrix,Matrix.of_apply] using h
def seedUpperQuot : (A ⧸ cofactorIdeal matrix) →+* ℂ :=
  Ideal.Quotient.lift _ seedLocalization (by
    change cofactorIdeal matrix ≤ RingHom.ker seedLocalization
    apply Ideal.span_le.mpr
    rintro _ ⟨c,rfl⟩
    exact seed_cofactor c)
def seedUpperQuotAlg : (A ⧸ cofactorIdeal matrix) →ₐ[ℂ] ℂ :=
  { seedUpperQuot with
    commutes' := by
      intro z
      change seedLocalization (algebraMap P A (C z)) = z
      simp [seedLocalization,seedPolynomial] }

#print axioms seedUpperQuotAlg
end
end UniformUpperGauge
