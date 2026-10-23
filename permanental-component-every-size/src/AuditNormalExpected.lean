import UniformNormalKernel

namespace UniformNormalAudit

theorem audit_denominator (l : ℕ) : 2*(l:ℂ)+1 ≠ 0 :=
  UniformBlockNormal.denominator_ne_zero l

theorem audit_diagonal (l : ℕ) : (-4*(2*(l:ℂ)-5)) ≠ 0 :=
  UniformBlockNormal.diagonal_ne_zero l

theorem audit_eigenvalue (l : ℕ) :
    (-4*(2*(l:ℂ)-5))+(l:ℂ)*(-32/(2*(l:ℂ)+1)) ≠ 0 :=
  UniformBlockNormal.eigenvalue_ne_zero l

theorem audit_literal_kernel (l : ℕ) (v : Fin l → ℂ)
    (h : ∀ i, (-4*(2*(l:ℂ)-5))*v i+(-32/(2*(l:ℂ)+1))*(∑ j, v j)=0) :
    v=0 := UniformBlockNormal.kernel_zero l v h

noncomputable def normalMatrix (l : ℕ) : Matrix (Fin l) (Fin l) ℂ :=
  fun i j => (if i=j then (-4*(2*(l:ℂ)-5)) else 0)+(-32/(2*(l:ℂ)+1))

theorem audit_actual_matrix_kernel (l : ℕ) (v : Fin l → ℂ)
    (h : (normalMatrix l).mulVec v = 0) : v=0 := by
  apply audit_literal_kernel l v
  intro i
  have hi := congrFun h i
  simpa [normalMatrix,Matrix.mulVec,dotProduct,add_mul,ite_mul,
    Finset.sum_add_distrib,← Finset.mul_sum] using hi

end UniformNormalAudit
#print axioms UniformBlockNormal.diagonal
#print axioms UniformBlockNormal.common
#print axioms UniformBlockNormal.denominator_ne_zero
#print axioms UniformBlockNormal.diagonal_ne_zero
#print axioms UniformBlockNormal.eigenvalue_identity
#print axioms UniformBlockNormal.eigenvalue_ne_zero
#print axioms UniformBlockNormal.kernel_zero
#print axioms UniformNormalAudit.audit_denominator
#print axioms UniformNormalAudit.audit_diagonal
#print axioms UniformNormalAudit.audit_eigenvalue
#print axioms UniformNormalAudit.audit_literal_kernel
#print axioms UniformNormalAudit.audit_actual_matrix_kernel
set_option pp.all true in
#check @UniformNormalAudit.audit_literal_kernel
set_option pp.all true in
#check @UniformNormalAudit.audit_actual_matrix_kernel
run_cmd do
  for n in (← Lean.getEnv).allImportedModuleNames do
    Lean.logInfo m!"AUDIT_IMPORT {n}"
