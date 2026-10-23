import ExceptionalCriticalFamily
import Mathlib.Tactic

set_option autoImplicit false
namespace ExceptionalIntrinsic
open ExceptionalCriticalFamily
variable {R : Type*} [CommRing R]

def P (d h j e f i : R) : R := e*i+e+f*h+f+h+i
def C0 (d h j e f i : R) : R := d*h+d*i+e*i+e*j+f*h+f*j
def C1 (d h j e f i : R) : R := d*i+d+f*j+f+i+j
def C2 (d h j e f i : R) : R := d*h+d+e*j+e+h+j
def E (d h j e : R) : R := (j+1)*e-eNumerator d h j
def I (d h j i : R) : R := (j-d)*(i+h)+(j-1)*(j+d)
def F (d h j f : R) : R := denominator d j*f-fNumerator d h j

theorem e_identity (d h j e f i : R) : E d h j e = C2 d h j e f i := by
  simp only [E,C2,eNumerator]; ring

theorem i_identity (d h j e f i : R) :
    2*I d h j i = -(j+1)*(C0 d h j e f i-P d h j e f i)+
      (j-1)*(C1 d h j e f i+C2 d h j e f i) := by
  simp only [I,C0,P,C1,C2]; ring

theorem i_clearing (d h j i : R) :
    denominator d j*i-iNumerator d h j = (j+1)*I d h j i := by
  simp only [denominator,iNumerator,I]; ring

theorem f_identity (d h j e f i : R) :
    F d h j f = (j-d)*C1 d h j e f i-(d+1)*I d h j i := by
  simp only [F,denominator,fNumerator,eNumerator,C1,I]; ring

theorem relation_identity (d h j e f i : R) :
    denominator d j*P d h j e f i - 2*relation d h j =
      (j-d)*C2 d h j e f i*(i+1)+(h+1)*(j-d)*C1 d h j e f i-
        2*((d+1)*h+d)*I d h j i := by
  simp only [denominator,P,relation,C2,C1,I]; ring

/-- Exact equations on the unit neighborhood of the exceptional basepoint.
This is a pointwise ring-valued equivalence, not yet a coordinate-ring isomorphism. -/
theorem constraints_iff (d h j e f i : R)
    (h2 : IsUnit (2 : R)) (hp : IsUnit (j+1)) (hm : IsUnit (j-d)) :
    (P d h j e f i = 0 ∧ C0 d h j e f i = 0 ∧ C1 d h j e f i = 0 ∧ C2 d h j e f i = 0) ↔
    (E d h j e = 0 ∧ I d h j i = 0 ∧ F d h j f = 0 ∧ relation d h j = 0) := by
  constructor
  · rintro ⟨hP,hC0,hC1,hC2⟩
    have hi : I d h j i = 0 := h2.mul_left_cancel (by
      simpa [hP,hC0,hC1,hC2] using i_identity d h j e f i)
    have hf : F d h j f = 0 := by rw [f_identity,hC1,hi]; ring
    have hr : relation d h j = 0 := by
      have he := relation_identity d h j e f i
      simp only [hP,hC1,hC2,hi,mul_zero,zero_mul,zero_add,sub_zero,zero_sub] at he
      exact h2.mul_left_cancel (by simpa using neg_eq_zero.mp he)
    exact ⟨by rw [e_identity,hC2],hi,hf,hr⟩
  · rintro ⟨he,hi,hf,hr⟩
    have hc2 : C2 d h j e f i = 0 := by rwa [e_identity] at he
    have hc1 : C1 d h j e f i = 0 := hm.mul_left_cancel (by
      simpa [hf,hi] using (f_identity d h j e f i).symm)
    have hD : IsUnit (denominator d j) := hp.mul hm
    have hP : P d h j e f i = 0 := hD.mul_left_cancel (by
      simpa [hr,hc1,hc2,hi] using relation_identity d h j e f i)
    have hc0 : C0 d h j e f i = 0 := by
      have heq := i_identity d h j e f i
      simp only [hi,hP,hc1,hc2,mul_zero,zero_add,sub_zero,add_zero] at heq
      exact hp.mul_left_cancel (by simpa using (neg_eq_zero.mp (by simpa only [neg_mul] using heq.symm)))
    exact ⟨hP,hc0,hc1,hc2⟩

#print axioms constraints_iff
end ExceptionalIntrinsic
