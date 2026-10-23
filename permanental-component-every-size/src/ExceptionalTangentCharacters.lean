import ExceptionalSignSymmetries

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ExceptionalTangentCharacters
open ExceptionalSignSymmetries
variable {R : Type*} [CommRing R]

def directions : Fin 4 → Mat R :=
  ![!![0,0,0,0,0;0,0,0,0,0;0,0,0,0,0;1,0,1,0,0;1,0,1,0,0],
    !![0,0,0,0,1;0,0,0,0,0;0,0,0,0,1;0,0,0,0,0;0,0,0,0,0],
    !![0,0,0,0,0;0,0,-1,1,0;0,0,0,0,0;0,0,0,0,0;0,0,0,0,0],
    !![0,0,0,0,0;0,0,0,0,0;0,1,0,-1,0;0,0,0,0,0;0,0,0,0,0]]
def project (M : Mat R) : Fin 4 → R :=
  ![M 4 0,M 0 4,M 1 3,M 2 1-M 0 0+M 2 0+M 0 1]
def torusTangent (r c : Fin 5 → R) : Mat R :=
  fun i j => (r i+c j)*PrimitiveFamily.A 0 i j

theorem projection_basis :
    (fun k => project (directions (R:=R) k)) = (1:Matrix (Fin 4) (Fin 4) R) := by
  ext k j
  fin_cases k <;> fin_cases j <;> norm_num [project,directions,Matrix.one_apply]

theorem projection_kills_torus (r c : Fin 5 → R) : project (torusTangent r c) = 0 := by
  ext k
  fin_cases k <;> norm_num [project,torusTangent,PrimitiveFamily.A] <;> ring

def signA (k : Fin 4) : R := if k=1 then -1 else 1
def signD (k : Fin 4) : R := if k=2 then -1 else 1
def signQ (k : Fin 4) : R := if k=3 then -1 else 1

theorem actionA_character (k : Fin 4) :
    actionA (directions (R:=R) k) = signA (R:=R) k • directions (R:=R) k := by
  ext r c
  fin_cases k <;> fin_cases r <;> fin_cases c <;>
    norm_num [actionA,negateColumn,Matrix.updateCol_apply,Matrix.submatrix,
      Equiv.swap_apply_def,directions,signA,Matrix.smul_apply]

theorem actionD_character_mod_torus (k : Fin 4) :
    actionD (directions (R:=R) k) = signD (R:=R) k • directions (R:=R) k +
      if k=2 then torusTangent ![0,1,0,0,0] 0 else 0 := by
  ext r c
  fin_cases k <;> fin_cases r <;> fin_cases c <;>
    norm_num [actionD,negateRow,Matrix.updateRow_apply,Matrix.submatrix,
      Equiv.swap_apply_def,directions,signD,Matrix.smul_apply,
      torusTangent,PrimitiveFamily.A]

theorem actionQ_character_mod_torus (k : Fin 4) :
    actionQ (directions (R:=R) k) = signQ (R:=R) k • directions (R:=R) k +
      if k=3 then torusTangent ![0,0,0,1,1] ![0,-1,0,-1,-1] else 0 := by
  ext r c
  fin_cases k <;> fin_cases r <;> fin_cases c <;>
    norm_num [actionQ,negateColumn,Matrix.updateCol_apply,Matrix.submatrix,
      Equiv.swap_apply_def,directions,signQ,Matrix.smul_apply,
      torusTangent,PrimitiveFamily.A]
end ExceptionalTangentCharacters
#print axioms ExceptionalTangentCharacters.projection_basis
#print axioms ExceptionalTangentCharacters.projection_kills_torus
#print axioms ExceptionalTangentCharacters.actionA_character
#print axioms ExceptionalTangentCharacters.actionD_character_mod_torus
#print axioms ExceptionalTangentCharacters.actionQ_character_mod_torus
