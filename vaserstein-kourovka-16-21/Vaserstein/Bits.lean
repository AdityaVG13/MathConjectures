import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Fin
import Vaserstein.Basic

/-!
# Matrices over `ZMod 2` as bit codes

A natural number `c` codes the `n × n` matrix whose `(i, j)` entry is bit `n * i + j` of `c`.
The functions here compute with codes using only operations that the Lean kernel evaluates on
binary numbers, and each comes with a lemma relating it to matrix arithmetic. They are used to
check the cases `n = 3` and `n = 4` by kernel computation.
-/

namespace Vaserstein.Bits

open Matrix

def bit (n c i j : ℕ) : Bool := c.testBit (n * i + j)

def xorUpTo (f : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => xor (xorUpTo f k) (f k)

def allUpTo (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | k + 1 => allUpTo p k && p k

def anyUpTo (p : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => anyUpTo p k || p k

/-- Entry `(i, j)` of the product of the matrices coded by `a` and `b`. -/
def mulEntry (n a b i j : ℕ) : Bool := xorUpTo (fun k => bit n a i k && bit n b k j) n

/-- The products of the matrices coded by `a, b` and by `c, d` agree. -/
def mulEq (n a b c d : ℕ) : Bool :=
  allUpTo (fun i => allUpTo (fun j => mulEntry n a b i j == mulEntry n c d i j) n) n

/-- The matrix coded by `c` sends some nonzero vector to zero. -/
def singular (n c : ℕ) : Bool :=
  anyUpTo (fun v => v != 0 &&
    allUpTo (fun i => !xorUpTo (fun k => bit n c i k && v.testBit k) n) n) (2 ^ n)

def toZ (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The matrix coded by `c`. -/
def ofCode (n c : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) := fun i j => toZ (bit n c i j)

theorem toZ_xor (a b : Bool) : toZ (xor a b) = toZ a + toZ b := by
  cases a <;> cases b <;> decide

theorem toZ_and (a b : Bool) : toZ (a && b) = toZ a * toZ b := by
  cases a <;> cases b <;> decide

theorem toZ_injective : Function.Injective toZ := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem allUpTo_eq_true {p : ℕ → Bool} {m : ℕ} : allUpTo p m = true ↔ ∀ k < m, p k = true := by
  induction m with
  | zero => simp [allUpTo]
  | succ m ih =>
    simp only [allUpTo, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      exacts [h1 k hk, h2]
    · intro h
      exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), h m (Nat.lt_succ_self m)⟩

theorem anyUpTo_eq_true {p : ℕ → Bool} {m : ℕ} : anyUpTo p m = true ↔ ∃ k < m, p k = true := by
  induction m with
  | zero => simp [anyUpTo]
  | succ m ih =>
    simp only [anyUpTo, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨k, hk, h⟩ | h)
      exacts [⟨k, Nat.lt_succ_of_lt hk, h⟩, ⟨m, Nat.lt_succ_self m, h⟩]
    · rintro ⟨k, hk, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      exacts [Or.inl ⟨k, hk, h⟩, Or.inr h]

theorem sum_toZ (f : ℕ → Bool) (m : ℕ) :
    ∑ k ∈ Finset.range m, toZ (f k) = toZ (xorUpTo f m) := by
  induction m with
  | zero => simp [xorUpTo, toZ]
  | succ m ih => rw [Finset.sum_range_succ, ih, xorUpTo, toZ_xor]

theorem ofCode_mul_apply (n a b : ℕ) (i j : Fin n) :
    (ofCode n a * ofCode n b) i j = toZ (mulEntry n a b i j) := by
  rw [Matrix.mul_apply, mulEntry, ← sum_toZ,
    ← Fin.sum_univ_eq_sum_range (fun k => toZ (bit n a i k && bit n b k j))]
  simp [ofCode, toZ_and]

theorem ofCode_mul_eq {n a b c d : ℕ} (h : mulEq n a b c d = true) :
    ofCode n a * ofCode n b = ofCode n c * ofCode n d := by
  ext i j
  rw [ofCode_mul_apply, ofCode_mul_apply]
  have := allUpTo_eq_true.1 (allUpTo_eq_true.1 h i i.2) j j.2
  rw [beq_iff_eq] at this
  rw [this]

/-- The vector coded by `v`. -/
def vecOf (n v : ℕ) : Fin n → ZMod 2 := fun k => toZ (v.testBit k)

theorem vecOf_ne_zero {n v : ℕ} (hv : v ≠ 0) (hvn : v < 2 ^ n) : vecOf n v ≠ 0 := by
  obtain ⟨k, hk⟩ := Nat.exists_testBit_of_ne_zero hv
  have hkn : k < n := by
    by_contra hkn
    have : v < 2 ^ k := lt_of_lt_of_le hvn (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow this] at hk
    exact Bool.false_ne_true hk
  intro h
  have := congrFun h ⟨k, hkn⟩
  simp [vecOf, hk, toZ] at this

theorem det_ofCode_eq_zero {n c : ℕ} (h : singular n c = true) : (ofCode n c).det = 0 := by
  obtain ⟨v, hvn, hv⟩ := anyUpTo_eq_true.1 h
  rw [Bool.and_eq_true, bne_iff_ne] at hv
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨vecOf n v, vecOf_ne_zero hv.1 hvn, ?_⟩
  ext i
  have hi := allUpTo_eq_true.1 hv.2 i i.2
  rw [Bool.not_eq_true'] at hi
  have : (ofCode n c *ᵥ vecOf n v) i =
      toZ (xorUpTo (fun k => bit n c i k && v.testBit k) n) := by
    rw [Matrix.mulVec, dotProduct, ← sum_toZ,
      ← Fin.sum_univ_eq_sum_range (fun k => toZ (bit n c i k && v.testBit k))]
    simp [ofCode, vecOf, toZ_and]
  rw [this, hi]
  rfl

/-! ### Coding a matrix -/

def bitsOf : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (bitsOf l)

theorem testBit_bitsOf (l : List Bool) (k : ℕ) : (bitsOf l).testBit k = l.getD k false := by
  induction l generalizing k with
  | nil => simp [bitsOf]
  | cons b l ih =>
    rcases k with _ | k
    · simp [bitsOf]
    · simp [bitsOf, Nat.testBit_bit_succ, ih]

theorem bitsOf_lt (l : List Bool) : bitsOf l < 2 ^ l.length := by
  induction l with
  | nil => simp [bitsOf]
  | cons b l ih =>
    rw [bitsOf, Nat.bit_val, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

/-- Entry `k = n * i + j` of a matrix, read as a bit. -/
def entryN {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) (k : ℕ) : Bool :=
  if h : k < n * n then
    M ⟨k / n, Nat.div_lt_of_lt_mul h⟩
      ⟨k % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; simp at h))⟩ == 1
  else false

/-- The code of a matrix. -/
def code {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) : ℕ :=
  bitsOf ((List.range (n * n)).map (entryN M))

theorem code_lt {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) : code M < 2 ^ (n * n) := by
  simpa [code] using bitsOf_lt ((List.range (n * n)).map (entryN M))

theorem ofCode_code {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) : ofCode n (code M) = M := by
  ext i j
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact i.elim0)
  have hk : n * i + j < n * n := by
    have := Nat.mul_le_mul_left n (Nat.succ_le_of_lt i.2)
    rw [Nat.mul_succ] at this
    omega
  have hdiv : (n * i + j) / n = i := by
    rw [Nat.mul_add_div hn, Nat.div_eq_of_lt j.2, add_zero]
  have hmod : (n * i + j) % n = j := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt j.2]
  simp only [ofCode, bit, code, testBit_bitsOf, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hk, Option.map_some, Option.getD_some, entryN, hk, ↓reduceDIte]
  have : (⟨(n * i + j) / n, Nat.div_lt_of_lt_mul hk⟩ : Fin n) = i := Fin.ext hdiv
  have h2 : (⟨(n * i + j) % n, Nat.mod_lt _ hn⟩ : Fin n) = j := Fin.ext hmod
  rw [this, h2]
  generalize M i j = x
  revert x
  decide

end Vaserstein.Bits
