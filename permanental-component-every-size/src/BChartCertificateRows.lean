import RankCertificate
import Mathlib.Tactic.Ring
/-! Literal emath043/046 polynomial data; no actual-equation provenance asserted here. -/
namespace BChartPolynomialCertificate
variable {R : Type*} [CommRing R]

@[simp] def coefficientRow0 (s : R) : Fin 15 → R :=
  ![(0 : R), (0 : R), ((-2) * s^4 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), ((-1) * s^3 : R), (0 : R), (1 * s^3 : R), (2 * s^4 + 1 * s^5 : R), ((-2) * s^3 : R), (0 : R)]

@[simp] def coefficientRow1 (s : R) : Fin 15 → R :=
  ![(0 : R), (0 : R), (4 * s^4 + 2 * s^5 : R), (0 : R), (0 : R), (0 : R), (1 * s^3 : R), (0 : R), ((-1) * s^3 : R), (0 : R), (1 * s^3 : R), (0 : R), ((-2) * s^4 + (-1) * s^5 : R), (0 : R), (0 : R)]

@[simp] def coefficientRow2 (s : R) : Fin 15 → R :=
  ![(0 : R), (0 : R), ((-2) * s^4 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (1 * s^3 : R), (0 : R), ((-1) * s^3 : R), (2 * s^4 + 1 * s^5 : R), (2 * s^3 : R), (0 : R)]

@[simp] def coefficientRow3 (s : R) : Fin 15 → R :=
  ![(0 : R), (0 : R), ((-2) * s^5 : R), (0 : R), (0 : R), (0 : R), ((-1) * s^3 : R), (0 : R), (1 * s^3 : R), (0 : R), ((-1) * s^3 : R), (0 : R), ((-2) * s^4 + (-1) * s^5 : R), (0 : R), (0 : R)]

@[simp] def coefficientRow4 (s : R) : Fin 15 → R :=
  ![(4 * s^4 + 2 * s^5 : R), ((-2) * s^4 : R), (0 : R), (0 : R), (0 : R), (0 : R), (1 * s^3 : R), (0 : R), ((-1) * s^3 : R), (0 : R), ((-1) * s^3 : R), (0 : R), (2 * s^4 + (-3) * s^5 + (-2) * s^6 : R), (0 : R), ((-2) * s^3 + 4 * s^4 + (-2) * s^5 : R)]

@[simp] def coefficientRow5 (s : R) : Fin 15 → R :=
  ![(0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (2 * s^4 : R), (0 : R), (0 : R), (0 : R), (2 * s^3 : R), (0 : R), (0 : R), (0 : R), (2 * s^3 : R), (0 : R)]

@[simp] def coefficientRow6 (s : R) : Fin 15 → R :=
  ![(0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (4 * s^4 + 2 * s^5 : R), ((-2) * s^3 : R), (0 : R), ((-2) * s^3 : R), (0 : R), (2 * s^3 : R), (2 * s^3 + 4 * s^4 : R), (4 * s^4 + (-4) * s^6 : R), ((-4) * s^3 + (-8) * s^4 : R), (0 : R)]

@[simp] def coefficientRow7 (s : R) : Fin 15 → R :=
  ![(0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (2 * s^4 : R), (0 : R), (0 : R), (0 : R), (2 * s^3 : R), (0 : R), (0 : R), (0 : R), (2 * s^3 : R), (0 : R)]

@[simp] def coefficientRow8 (s : R) : Fin 15 → R :=
  ![(0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (2 * s^5 : R), (0 : R), (0 : R), (0 : R), (2 * s^3 : R), (0 : R), (0 : R), (0 : R), (4 * s^3 + 16 * s^4 : R), (0 : R)]

@[simp] def coefficientRow9 (s : R) : Fin 15 → R :=
  ![(0 : R), (0 : R), (0 : R), (2 * s^4 : R), (2 * s^5 : R), (0 : R), (0 : R), (4 * s^4 + 2 * s^5 : R), (0 : R), (2 * s^3 + 4 * s^4 : R), (0 : R), (0 : R), (0 : R), ((-4) * s^3 + (-2) * s^4 : R), ((-2) * s^3 + 2 * s^4 : R)]

@[simp] def coefficientRow10 (s : R) : Fin 15 → R :=
  ![(0 : R), (0 : R), (2 * s^3 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), ((-1) * s^2 : R), (0 : R), ((-1) * s^2 : R), ((-2) * s^3 + (-1) * s^4 : R), ((-2) * s^2 : R), (0 : R)]

@[simp] def coefficientRow11 (s : R) : Fin 15 → R :=
  ![(0 : R), (0 : R), (4 * s^3 + 2 * s^4 : R), (0 : R), (0 : R), (0 : R), (1 * s^2 : R), (0 : R), ((-1) * s^2 : R), (0 : R), (1 * s^2 : R), (0 : R), ((-2) * s^3 + (-1) * s^4 : R), (0 : R), (0 : R)]

@[simp] def coefficientRow12 (s : R) : Fin 15 → R :=
  ![(0 : R), (0 : R), (2 * s^3 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (1 * s^2 : R), (0 : R), (1 * s^2 : R), ((-2) * s^3 + (-1) * s^4 : R), (2 * s^2 : R), (0 : R)]

@[simp] def coefficientRow13 (s : R) : Fin 15 → R :=
  ![(0 : R), (0 : R), (2 * s^4 : R), (0 : R), (0 : R), (0 : R), (1 * s^2 : R), (0 : R), ((-1) * s^2 : R), (0 : R), (1 * s^2 : R), (0 : R), (2 * s^3 + 1 * s^4 : R), (0 : R), (0 : R)]

@[simp] def coefficientRow14 (s : R) : Fin 15 → R :=
  ![(4 * s^3 + 2 * s^4 : R), (2 * s^3 : R), (0 : R), (0 : R), (0 : R), (0 : R), ((-1) * s^2 : R), (0 : R), (1 * s^2 : R), (0 : R), (1 * s^2 : R), (0 : R), ((-2) * s^3 + 3 * s^4 + 2 * s^5 : R), (0 : R), ((-2) * s^2 + 4 * s^3 + (-2) * s^4 : R)]

@[simp] def coefficientRow15 (s : R) : Fin 15 → R :=
  ![((-2) * s^2 : R), (0 : R), (0 : R), (0 : R), (1 * s^2 : R), ((-1) * s^2 : R), (0 : R), (1 * s^2 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (1 * s : R), (1 * s + 2 * s^2 : R)]

@[simp] def coefficientRow16 (s : R) : Fin 15 → R :=
  ![(0 : R), ((-2) * s^2 : R), (2 * s^2 + 4 * s^3 : R), ((-1) * s^2 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), ((-2) * s^2 + 4 * s^3 + (-2) * s^4 : R), (0 : R), (1 * s + 2 * s^2 : R)]

@[simp] def coefficientRow17 (s : R) : Fin 15 → R :=
  ![((-2) * s^2 : R), (0 : R), (0 : R), (0 : R), ((-1) * s^2 : R), (1 * s^2 : R), (0 : R), ((-1) * s^2 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), ((-1) * s : R), (1 * s + 2 * s^2 : R)]

@[simp] def coefficientRow18 (s : R) : Fin 15 → R :=
  ![((-2) * s^2 : R), (0 : R), (0 : R), ((-1) * s^2 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), ((-1) * s + (-2) * s^2 : R)]

@[simp] def coefficientRow19 (s : R) : Fin 15 → R :=
  ![(2 * s^2 + 4 * s^3 : R), (0 : R), (0 : R), (1 * s^2 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (1 * s + (-4) * s^3 : R)]

@[simp] def coefficientRow20 (s : R) : Fin 15 → R :=
  ![(2 * s^2 : R), (0 : R), (0 : R), (0 : R), ((-1) * s^2 : R), ((-1) * s^2 : R), (0 : R), ((-1) * s^2 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (1 * s : R), ((-1) * s + (-2) * s^2 : R)]

@[simp] def coefficientRow21 (s : R) : Fin 15 → R :=
  ![(0 : R), (2 * s^2 : R), (2 * s^2 + 4 * s^3 : R), (1 * s^2 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), ((-2) * s^2 + 4 * s^3 + (-2) * s^4 : R), (0 : R), ((-1) * s + (-2) * s^2 : R)]

@[simp] def coefficientRow22 (s : R) : Fin 15 → R :=
  ![(2 * s^2 : R), (0 : R), (0 : R), (0 : R), (1 * s^2 : R), (1 * s^2 : R), (0 : R), (1 * s^2 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), ((-1) * s : R), ((-1) * s + (-2) * s^2 : R)]

@[simp] def coefficientRow23 (s : R) : Fin 15 → R :=
  ![(2 * s^2 : R), (0 : R), (0 : R), (1 * s^2 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (1 * s + 2 * s^2 : R)]

@[simp] def coefficientRow24 (s : R) : Fin 15 → R :=
  ![(2 * s^2 + 4 * s^3 : R), (0 : R), (0 : R), (1 * s^2 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (1 * s + (-4) * s^3 : R)]

def coefficientMatrix (s : R) : Matrix (Fin 25) (Fin 15) R :=
  ![coefficientRow0 s, coefficientRow1 s, coefficientRow2 s, coefficientRow3 s, coefficientRow4 s, coefficientRow5 s, coefficientRow6 s, coefficientRow7 s, coefficientRow8 s, coefficientRow9 s, coefficientRow10 s, coefficientRow11 s, coefficientRow12 s, coefficientRow13 s, coefficientRow14 s, coefficientRow15 s, coefficientRow16 s, coefficientRow17 s, coefficientRow18 s, coefficientRow19 s, coefficientRow20 s, coefficientRow21 s, coefficientRow22 s, coefficientRow23 s, coefficientRow24 s]

@[simp] def inverseRow0 (s : R) : Fin 15 → R :=
  ![(0 : R), (0 : R), (0 : R), (2 + 4 * s : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (2 * s + 4 * s^2 : R), (4 * s^2 + (-8) * s^3 + 4 * s^4 : R), (0 : R), (4 * s^2 + (-8) * s^3 + 4 * s^4 : R), (0 : R), (0 : R)]

@[simp] def inverseRow1 (s : R) : Fin 15 → R :=
  ![(0 : R), (0 : R), (0 : R), (6 + 12 * s : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (6 * s + 12 * s^2 : R), (12 * s^2 + 12 * s^3 + 12 * s^4 : R), ((-18) * s^3 : R), (12 * s^2 + 12 * s^3 + 12 * s^4 : R), (36 * s^3 : R), (18 * s^3 : R)]

@[simp] def inverseRow2 (s : R) : Fin 15 → R :=
  ![(4 + (-8) * s + 4 * s^2 : R), (0 : R), (4 + (-8) * s + 4 * s^2 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (4 * s^2 + 2 * s^3 : R), (0 : R), (0 : R), (4 * s^2 + 2 * s^3 : R)]

@[simp] def inverseRow3 (s : R) : Fin 15 → R :=
  ![(0 : R), (0 : R), (0 : R), ((-8) + (-16) * s : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), ((-8) * s + (-16) * s^2 : R), ((-16) * s^2 + (-4) * s^3 + (-16) * s^4 : R), (0 : R), ((-16) * s^2 + (-4) * s^3 + (-16) * s^4 : R), ((-72) * s^3 : R), (0 : R)]

@[simp] def inverseRow4 (s : R) : Fin 15 → R :=
  ![((-8) + 16 * s + (-8) * s^2 : R), (0 : R), (0 : R), ((-6) + (-6) * s : R), (44 * s + 28 * s^2 : R), (0 : R), ((-8) + (-10) * s : R), ((-18) * s : R), ((-8) * s + 16 * s^2 + (-8) * s^3 : R), ((-6) * s + (-6) * s^2 : R), ((-12) * s^2 + 36 * s^3 + 12 * s^4 : R), (0 : R), ((-12) * s^2 + (-36) * s^3 + (-24) * s^4 : R), ((-36) * s^3 : R), (0 : R)]

@[simp] def inverseRow5 (s : R) : Fin 15 → R :=
  ![(4 + 32 * s : R), (0 : R), (0 : R), (0 : R), (32 * s : R), (0 : R), (4 : R), (0 : R), (4 * s + 32 * s^2 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R)]

@[simp] def inverseRow6 (s : R) : Fin 15 → R :=
  ![(60 * s^2 + 24 * s^3 + (-12) * s^4 : R), (36 * s^2 : R), (12 * s^2 + (-36) * s^3 + (-12) * s^4 : R), (0 : R), (36 * s^2 + 24 * s^3 : R), ((-18) * s^2 : R), ((-6) * s^2 : R), (0 : R), (12 * s^3 + (-12) * s^4 : R), (0 : R), (0 : R), ((-6) * s^4 + (-6) * s^5 : R), (0 : R), (0 : R), ((-6) * s^4 + (-6) * s^5 : R)]

@[simp] def inverseRow7 (s : R) : Fin 15 → R :=
  ![(8 + 20 * s + 8 * s^2 : R), (0 : R), (0 : R), (6 + 6 * s : R), ((-8) * s + (-28) * s^2 : R), (0 : R), (8 + 10 * s : R), (18 * s : R), (8 * s + 20 * s^2 + 8 * s^3 : R), (6 * s + 6 * s^2 : R), (12 * s^2 + (-12) * s^4 : R), (0 : R), (12 * s^2 + 24 * s^4 : R), (36 * s^3 : R), (0 : R)]

@[simp] def inverseRow8 (s : R) : Fin 15 → R :=
  ![(8 * s + 40 * s^2 + 4 * s^3 + (-16) * s^4 : R), (0 : R), (8 * s + (-8) * s^2 + (-56) * s^3 + (-16) * s^4 : R), ((-6) * s + (-30) * s^2 : R), (36 * s^2 + 24 * s^3 : R), ((-18) * s^2 : R), ((-6) * s^2 : R), (0 : R), (12 * s^3 + (-12) * s^4 : R), ((-6) * s^2 + 6 * s^3 : R), ((-12) * s^3 + (-12) * s^4 + (-12) * s^5 : R), (8 * s^3 + 12 * s^4 + (-8) * s^5 : R), ((-12) * s^3 + (-12) * s^4 + (-12) * s^5 : R), ((-36) * s^4 : R), (8 * s^3 + (-24) * s^4 + (-8) * s^5 : R)]

@[simp] def inverseRow9 (s : R) : Fin 15 → R :=
  ![((-8) * s + (-28) * s^2 : R), (0 : R), (0 : R), (0 : R), (8 * s^2 : R), (0 : R), ((-8) * s : R), (0 : R), ((-8) * s^2 + (-28) * s^3 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R)]

@[simp] def inverseRow10 (s : R) : Fin 15 → R :=
  ![(24 * s^2 + (-12) * s^3 + (-12) * s^4 : R), (36 * s^2 : R), (24 * s^2 + (-12) * s^3 + (-12) * s^4 : R), ((-6) * s + (-30) * s^2 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), ((-6) * s^2 + 6 * s^3 : R), ((-12) * s^3 + (-12) * s^4 + (-12) * s^5 : R), (6 * s^4 + (-6) * s^5 : R), ((-12) * s^3 + (-12) * s^4 + (-12) * s^5 : R), ((-36) * s^4 : R), ((-30) * s^4 + (-6) * s^5 : R)]

@[simp] def inverseRow11 (s : R) : Fin 15 → R :=
  ![(0 : R), (0 : R), ((-36) * s^2 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), ((-36) * s^3 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R)]

@[simp] def inverseRow12 (s : R) : Fin 15 → R :=
  ![(4 + 8 * s : R), (0 : R), (4 + 8 * s : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (4 * s^2 : R), (0 : R), (0 : R), (4 * s^2 : R)]

@[simp] def inverseRow13 (s : R) : Fin 15 → R :=
  ![(4 * s + (-4) * s^2 : R), (0 : R), (0 : R), (0 : R), ((-4) * s^2 : R), (0 : R), (4 * s : R), (0 : R), (4 * s^2 + (-4) * s^3 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R)]

@[simp] def inverseRow14 (s : R) : Fin 15 → R :=
  ![(0 : R), (0 : R), (0 : R), (4 * s : R), (0 : R), (0 : R), (0 : R), (0 : R), (0 : R), (4 * s^2 : R), (8 * s^3 + 4 * s^4 : R), (0 : R), (8 * s^3 + 4 * s^4 : R), (0 : R), (0 : R)]

def scaledInverse (s : R) : Matrix (Fin 15) (Fin 15) R :=
  ![inverseRow0 s, inverseRow1 s, inverseRow2 s, inverseRow3 s, inverseRow4 s, inverseRow5 s, inverseRow6 s, inverseRow7 s, inverseRow8 s, inverseRow9 s, inverseRow10 s, inverseRow11 s, inverseRow12 s, inverseRow13 s, inverseRow14 s]

def selectedMatrix (s : R) : Matrix (Fin 15) (Fin 15) R :=
  (coefficientMatrix s).submatrix LocalGeometryRank.selectedRows id

def rankScale (s : R) : R := 72 * s^5
end BChartPolynomialCertificate
