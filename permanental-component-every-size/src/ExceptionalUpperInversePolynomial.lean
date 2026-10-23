import ExceptionalBranchQuadratic

set_option autoImplicit false
namespace ExceptionalUpper
open ExceptionalCriticalFamily
variable {R : Type*} [CommRing R]

def T (d h j p c0 c1 c2 : R) : R := -(j+1)*(c0-p)+(j-1)*(c1+c2)
def K (d h j p c0 c1 c2 : R) : R :=
  4*relation d h j-2*denominator d j*p+
  c2*(T d h j p c0 c1 c2+2*(j-d)*(1-h)-2*(j-1)*(j+d))+
  2*(h+1)*(j-d)*c1-2*((d+1)*h+d)*T d h j p c0 c1 c2

def A (d h p c0 c1 c2 : R) : R := 4*ExceptionalBranch.alpha d h-2*p-2*c2
def B (d h p c0 c1 c2 : R) : R :=
  4*ExceptionalBranch.beta d h-2*p*(1-d)+
  c2*(-c0+p+c1+c2+4-2*h-2*d)+2*(h+1)*c1-2*((d+1)*h+d)*(-c0+p+c1+c2)
def C (d h p c0 c1 c2 : R) : R :=
  4*ExceptionalBranch.gamma d h+2*p*d+c2*(-c0+p-c1-c2+2*d*h)-
  2*d*(h+1)*c1-2*((d+1)*h+d)*(-c0+p-c1-c2)

def eOut (d h j p c0 c1 c2 : R) : R :=
  2*(c2+eNumerator d h j)*(j-d)
def iOut (d h j p c0 c1 c2 : R) : R :=
  (j+1)*(T d h j p c0 c1 c2-2*(j-d)*h-2*(j-1)*(j+d))
def fOut (d h j p c0 c1 c2 : R) : R :=
  2*(j-d)*c1-(d+1)*T d h j p c0 c1 c2+2*fNumerator d h j

theorem quadratic_identity (d h j p c0 c1 c2 : R) :
    K d h j p c0 c1 c2 = A d h p c0 c1 c2*j^2+B d h p c0 c1 c2*j+C d h p c0 c1 c2 := by
  simp only [K,T,A,B,C,ExceptionalBranch.alpha,ExceptionalBranch.beta,ExceptionalBranch.gamma,
    relation,denominator]
  ring

theorem c1_identity (d h j p c0 c1 c2 : R) :
    (d+1)*iOut d h j p c0 c1 c2+(j+1)*fOut d h j p c0 c1 c2+
      (d+j)*(2*denominator d j) = c1*(2*denominator d j) := by
  simp only [iOut,fOut,T,denominator,fNumerator,eNumerator]; ring

theorem c2_identity (d h j p c0 c1 c2 : R) :
    (j+1)*eOut d h j p c0 c1 c2+((d+1)*h+d+j)*(2*denominator d j) =
      c2*(2*denominator d j) := by
  simp only [eOut,denominator,eNumerator]; ring

def clearedP (d h j p c0 c1 c2 : R) : R :=
  let E := eOut d h j p c0 c1 c2
  let F := fOut d h j p c0 c1 c2
  let I := iOut d h j p c0 c1 c2
  let D := 2*denominator d j
  E*I+E*D+F*h*D+F*D+h*D^2+I*D

def clearedC0 (d h j p c0 c1 c2 : R) : R :=
  let E := eOut d h j p c0 c1 c2
  let F := fOut d h j p c0 c1 c2
  let I := iOut d h j p c0 c1 c2
  let D := 2*denominator d j
  d*h*D^2+d*I*D+E*I+E*j*D+F*h*D+F*j*D

theorem p_identity (d h j p c0 c1 c2 : R) :
    clearedP d h j p c0 c1 c2-p*(2*denominator d j)^2 =
      2*denominator d j*K d h j p c0 c1 c2 := by
  simp only [clearedP,eOut,fOut,iOut,T,K,relation,denominator,eNumerator,fNumerator]
  ring

theorem c0_identity (d h j p c0 c1 c2 : R) :
    clearedC0 d h j p c0 c1 c2-c0*(2*denominator d j)^2 =
      2*denominator d j*K d h j p c0 c1 c2 := by
  simp only [clearedC0,eOut,fOut,iOut,T,K,relation,denominator,eNumerator,fNumerator]
  ring

#print axioms quadratic_identity
#print axioms p_identity
#print axioms c0_identity
end ExceptionalUpper
