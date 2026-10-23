import ExceptionalExpansion
import ExceptionalStationaryJacobian
import ParametricMatrix

/-! Exact univariate curve certificates from emath062/063. The curve is evaluated
in the actual translated matrix N_0. The stationary cofactors have order at least4,
and its full permanent has leading term -18 z^5. These finite identities do not
assert the formal Morse theorem or historical novelty. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace ExceptionalDiagonalCurve
open ConcreteLocalGeometry ParametricLocalGeometry ExceptionalStationaryJacobian
open ExceptionalExpansion

noncomputable def ys (z : ℂ) : Fin 12 → ℂ :=
  ![(-1/2) * z^2 + (-3/4) * z^3,
    (-3/2) * z^2 + (-13/4) * z^3,
    (1) * z^2 + (-4) * z^3,
    (2) * z^2 + (3) * z^3,
    (1) * z^3,
    (-1) * z^2 + (2) * z^3,
    0,
    (-7/2) * z^3,
    (7/2) * z^3,
    (-3/2) * z^3,
    (3/2) * z^3,
    0]
noncomputable def curveAssignment (z : ℂ) : Fin 16 → ℂ :=
  ![z,z,z,z,ys z 0,ys z 1,ys z 2,ys z 3,ys z 4,ys z 5,
    ys z 6,ys z 7,ys z 8,ys z 9,ys z 10,ys z 11]
noncomputable def evalCurve (z : ℂ) : P →+* ℂ :=
  MvPolynomial.eval₂Hom (RingHom.id ℂ) (curveAssignment z)
noncomputable def curveMatrix (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun r c => evalCurve z (translatedN 0 r c)
noncomputable def formula (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  let da := 1-(z+1)*z
  let dq := 1+2*z-z*z
  let dd := 1+z*z
  let den := da*dq*dd
  let jn := z*(1+z)*dq*dd
  let kn := -z*z*da*dd
  let zn := z*(1+z)*da*dq
  !![1,1,1,1,z;
     1,ys z 0,-1-z+ys z 1,z,ys z 2;
     1,z-1,1+ys z 3,1-z+ys z 4,z+ys z 5;
     jn+den*ys z 6,kn+den*ys z 7,jn+zn-z*den+den*ys z 8,den,den;
     z*den,kn+den*ys z 9,zn+den*ys z 10,den,-den+den*ys z 11]

theorem curve_matrix_formula (z : ℂ) : curveMatrix z = formula z := by
  ext r c
  change evalCurve z (translatedN 0 r c) = formula z r c
  rw [translatedN_eq_matrixWithParameter]
  fin_cases r <;> fin_cases c <;>
    norm_num [evalCurve,matrixWithParameter,x,curveAssignment,formula,ys] <;> ring

noncomputable def potentialValue (z : ℂ) : ℂ :=
  (-18) * z^5 + (-63) * z^6 + (-27/2) * z^7 + (207) * z^8 + (137) * z^9 + (-867/4) * z^10 + (659/4) * z^11 + (-1329/4) * z^12 + (395/2) * z^13 + (-869) * z^14 + (7543/4) * z^15 + (1935/4) * z^16 + (602) * z^17 + (3415/2) * z^18 + (-2393/4) * z^19 + (-137/2) * z^20 + (869/2) * z^21 + (-907/4) * z^22 + (-343/4) * z^23 + (42) * z^24
noncomputable def cofactorQuotient (z : ℂ) : Fin 12 → ℂ :=
  ![(16) * z^0 + (37) * z^1 + (-59) * z^2 + (-76) * z^3 + (33) * z^4 + (-211) * z^5 + (319/2) * z^6 + (235/2) * z^7 + (1/2) * z^8 + (186) * z^9 + (47) * z^10 + (-24) * z^11 + (63) * z^12 + (4) * z^13 + (-63/2) * z^14 + (-3/2) * z^15 + (7/2) * z^16,
    (-2) * z^0 + (-27) * z^1 + (3) * z^2 + (87) * z^3 + (-62) * z^4 + (144) * z^5 + (-65/2) * z^6 + (-173/2) * z^7 + (43/2) * z^8 + (-125) * z^9 + (-97) * z^10 + (-10) * z^11 + (-50) * z^12 + (61/2) * z^14 + (3/2) * z^15 + (-7/2) * z^16,
    (-17) * z^0 + (-24) * z^1 + (48) * z^2 + (99/2) * z^3 + (143) * z^4 + (55) * z^5 + (-108) * z^6 + (87) * z^7 + (-659) * z^8 + (-565/2) * z^9 + (-197) * z^10 + (-837/2) * z^11 + (152) * z^12 + (34) * z^13 + (-103) * z^14 + (54) * z^15 + (21) * z^16 + (-21/2) * z^17,
    (-10) * z^0 + (-73/2) * z^1 + (95/4) * z^2 + (128) * z^3 + (-1) * z^4 + (-19/4) * z^5 + (-191/2) * z^6 + (-186) * z^7 + (36) * z^8 + (222) * z^9 + (619/4) * z^10 + (138) * z^11 + (37) * z^12 + (-347/4) * z^13 + (-21) * z^14 + (14) * z^15,
    (8) * z^0 + (29) * z^1 + (33/4) * z^2 + (-137/4) * z^3 + (423/4) * z^4 + (117/2) * z^5 + (-493) * z^6 + (-567/2) * z^7 + (-1539/4) * z^8 + (-387/4) * z^9 + (49/4) * z^10 + (767) * z^11 + (687/4) * z^12 + (773/4) * z^13 + (575/2) * z^14 + (-893/4) * z^15 + (-343/4) * z^16 + (42) * z^17,
    (-31/2) * z^0 + (-71/2) * z^1 + (73/4) * z^2 + (233/4) * z^3 + (281/4) * z^4 + (55/2) * z^5 + (33/2) * z^6 + (121/4) * z^7 + (267/4) * z^8 + (81/2) * z^9 + (44) * z^10 + (-159/4) * z^11 + (-75/2) * z^12 + (29/2) * z^13 + (21/4) * z^14 + (-7/4) * z^15,
    (-51/4) * z^0 + (17/2) * z^1 + (-35/4) * z^2 + (137/4) * z^3 + (-4) * z^4 + (53) * z^5 + (69) * z^6 + (-361/4) * z^7 + (-38) * z^8 + (-361/4) * z^9 + (-153/4) * z^10 + (93/4) * z^11 + (15/4) * z^12,
    (-101/4) * z^0 + (-27) * z^1 + (257/4) * z^2 + (-16) * z^3 + (287/4) * z^4 + (141/4) * z^5 + (83) * z^6 + (177/2) * z^7 + (-11) * z^8 + (25/4) * z^9 + (17/4) * z^10 + (-6) * z^11,
    (-31/4) * z^0 + (-7) * z^1 + (111/4) * z^2 + (4) * z^3 + (-123/4) * z^4 + (255/4) * z^5 + (-26) * z^6 + (29/2) * z^7 + (32) * z^8 + (-129/4) * z^9 + (-33/4) * z^10 + (6) * z^11,
    (5/4) * z^0 + (-47/2) * z^1 + (-291/4) * z^2 + (12) * z^3 + (21/4) * z^4 + (-543/4) * z^5 + (435/4) * z^6 + (-35) * z^7 + (-69) * z^8 + (281/4) * z^9 + (35/2) * z^10 + (-14) * z^11,
    (-41/4) * z^0 + (-33/2) * z^1 + (171/4) * z^2 + (28) * z^3 + (-353/4) * z^4 + (427/4) * z^5 + (-247/4) * z^6 + (-14) * z^7 + (62) * z^8 + (-249/4) * z^9 + (-35/2) * z^10 + (14) * z^11,
    (-17/4) * z^0 + (-19/4) * z^1 + (5) * z^2 + (-85/4) * z^3 + (-45/2) * z^4 + (57) * z^5 + (-43/4) * z^6 + (10) * z^7 + (23/4) * z^8 + (-179/4) * z^9 + (-21/4) * z^10 + (35/4) * z^11]

theorem potential_identity (z : ℂ) : (curveMatrix z).permanent = potentialValue z := by
  rw [curve_matrix_formula]
  norm_num [permanent_succ_column_zero,Fin.sum_univ_succ,Matrix.submatrix,
    Fin.succAbove,formula,ys,potentialValue]
  ring

theorem stationary_order_four (z : ℂ) (k : Fin 12) :
    ((curveMatrix z).submatrix (principalPairs k).1.succAbove
      (principalPairs k).2.succAbove).permanent = z^4 * cofactorQuotient z k := by
  rw [curve_matrix_formula]
  fin_cases k
  all_goals norm_num [permanent_succ_column_zero,Fin.sum_univ_succ,Matrix.submatrix,
    Fin.succAbove,formula,ys,principalPairs,cofactorQuotient]
  all_goals ring
end ExceptionalDiagonalCurve
#print axioms ExceptionalDiagonalCurve.curve_matrix_formula
#print axioms ExceptionalDiagonalCurve.potential_identity
#print axioms ExceptionalDiagonalCurve.stationary_order_four
