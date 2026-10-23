import Vaserstein.Bits

/-!
# Checking covering by certificates

`scanAll` walks through every code of an `n × n` matrix and checks, for each one, either that the
matrix is singular or that a supplied certificate conjugates it to one of a list of class
representatives. `witOK` checks, for each pair of nonidentity representatives `(a, b)`, a supplied
product of `n` conjugates of `a` that equals `b`. `covers_of_certs` turns these two checks into the
statement that every nonidentity element of `GL_n(2)` is a product of `n` conjugates of any given
nonidentity element.
-/

namespace Vaserstein.Bits

open Matrix

/-- `x = P · rep_r · Q` with `P Q = 1`, for some representative index `r`. -/
def Cert (n : ℕ) (reps : List ℕ) (idc x : ℕ) : Prop :=
  ∃ r < reps.length, ∃ P Q : ℕ, mulEq n x P P (reps.getD r 0) = true ∧ mulEq n P Q idc idc = true

/-- Check the codes `c, …, c + fuel - 1`. The number `d` packs, lowest bits first, one certificate
`(x, r, P, Q)` of `3 n² + 4` bits for each code `x` that is not shown singular, in increasing
order of `x`. -/
def scan (n : ℕ) (reps : List ℕ) (idc : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, d => d == 0
  | fuel + 1, c, d =>
    if d != 0 && d % 2 ^ (n * n) == c then
      ((d >>> (n * n)) % 16 < reps.length &&
        mulEq n c ((d >>> (n * n + 4)) % 2 ^ (n * n)) ((d >>> (n * n + 4)) % 2 ^ (n * n))
          (reps.getD ((d >>> (n * n)) % 16) 0) &&
        mulEq n ((d >>> (n * n + 4)) % 2 ^ (n * n)) ((d >>> (2 * (n * n) + 4)) % 2 ^ (n * n))
          idc idc) &&
      scan n reps idc fuel (c + 1) (d >>> (3 * (n * n) + 4))
    else singular n c && scan n reps idc fuel (c + 1) d

theorem scan_spec {n : ℕ} {reps : List ℕ} {idc : ℕ} :
    ∀ fuel c d, scan n reps idc fuel c d = true →
      ∀ x, c ≤ x → x < c + fuel → singular n x = true ∨ Cert n reps idc x := by
  intro fuel
  induction fuel with
  | zero => intro c d _ x h1 h2; omega
  | succ fuel ih =>
    intro c d h x h1 h2
    unfold scan at h
    split at h
    · rw [Bool.and_eq_true] at h
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · right
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨_, h.1.1.1, _, _, h.1.1.2, h.1.2⟩
      · exact ih _ _ h.2 x h1 (by omega)
    · rw [Bool.and_eq_true] at h
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · exact Or.inl h.1
      · exact ih _ _ h.2 x h1 (by omega)

/-- Check all codes from `base` on, `size` codes per chunk. -/
def scanAll (n : ℕ) (reps : List ℕ) (idc size : ℕ) : ℕ → List ℕ → Bool
  | base, [] => decide (2 ^ (n * n) ≤ base)
  | base, d :: ds => scan n reps idc size base d && scanAll n reps idc size (base + size) ds

theorem scanAll_cons_of {n : ℕ} {reps : List ℕ} {idc size base d : ℕ} {ds : List ℕ}
    (h : scan n reps idc size base d = true)
    (h' : scanAll n reps idc size (base + size) ds = true) :
    scanAll n reps idc size base (d :: ds) = true := by
  rw [scanAll, h, h', Bool.and_self]

theorem scanAll_nil_of {n : ℕ} {reps : List ℕ} {idc size base : ℕ} (h : 2 ^ (n * n) ≤ base) :
    scanAll n reps idc size base [] = true := by
  simpa [scanAll] using h

theorem scanAll_spec {n : ℕ} {reps : List ℕ} {idc size : ℕ} :
    ∀ ds base, scanAll n reps idc size base ds = true →
      ∀ x, base ≤ x → x < 2 ^ (n * n) → singular n x = true ∨ Cert n reps idc x := by
  intro ds
  induction ds with
  | nil => intro base h x h1 h2; simp [scanAll] at h; omega
  | cons d ds ih =>
    intro base h x h1 h2
    rw [scanAll, Bool.and_eq_true] at h
    by_cases hx : x < base + size
    · exact scan_spec _ _ _ h.1 x h1 hx
    · exact ih _ h.2 x (by omega) h2

/-- A product chain: each `c = P · rep · Q` with `P Q = 1`, and the running product moves from
`s` to the next `s'`, ending at `t`. -/
def chainOK (n ra idc : ℕ) : ℕ → List (ℕ × ℕ × ℕ × ℕ) → ℕ → Bool
  | s, [], t => s == t
  | s, (c, P, Q, s') :: l, t =>
    mulEq n c P P ra && mulEq n P Q idc idc && mulEq n s c s' idc && chainOK n ra idc s' l t

/-- The invertible matrix coded by `P`, given a code `Q` of its inverse. -/
def mkGL {n P Q idc : ℕ} (hid : ofCode n idc = 1) (h : mulEq n P Q idc idc = true) :
    GL (Fin n) (ZMod 2) :=
  have h1 : ofCode n P * ofCode n Q = 1 := by rw [ofCode_mul_eq h, hid, one_mul]
  ⟨ofCode n P, ofCode n Q, h1, mul_eq_one_comm.1 h1⟩

theorem val_mkGL {n P Q idc : ℕ} (hid : ofCode n idc = 1) (h : mulEq n P Q idc idc = true) :
    ((mkGL hid h : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = ofCode n P := rfl

theorem val_inv_mkGL {n P Q idc : ℕ} (hid : ofCode n idc = 1) (h : mulEq n P Q idc idc = true) :
    (((mkGL hid h)⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = ofCode n Q := rfl

/-- If `x P = P r` and `P Q = 1` then `x = P r P⁻¹`. -/
theorem conj_eq {n x P Q r idc : ℕ} (hid : ofCode n idc = 1) (hc : mulEq n x P P r = true)
    (h : mulEq n P Q idc idc = true) :
    ofCode n x = ofCode n P * ofCode n r * ofCode n Q := by
  have h1 : ofCode n P * ofCode n Q = 1 := by rw [ofCode_mul_eq h, hid, one_mul]
  rw [← ofCode_mul_eq hc, Matrix.mul_assoc, h1, Matrix.mul_one]

open Pointwise in
theorem chainOK_spec {n ra idc : ℕ} (hid : ofCode n idc = 1) (A : GL (Fin n) (ZMod 2))
    (hA : (A : Matrix (Fin n) (Fin n) (ZMod 2)) = ofCode n ra) :
    ∀ (l : List (ℕ × ℕ × ℕ × ℕ)) (s t : ℕ) (X : GL (Fin n) (ZMod 2)) (k : ℕ),
      chainOK n ra idc s l t = true → (X : Matrix (Fin n) (Fin n) (ZMod 2)) = ofCode n s →
      X ∈ conjugatesOf A ^ k →
      ∃ Y ∈ conjugatesOf A ^ (k + l.length), (Y : Matrix (Fin n) (Fin n) (ZMod 2)) = ofCode n t := by
  intro l
  induction l with
  | nil =>
    intro s t X k h hX hk
    simp only [chainOK, beq_iff_eq] at h
    exact ⟨X, by simpa using hk, h ▸ hX⟩
  | cons e l ih =>
    obtain ⟨c, P, Q, s'⟩ := e
    intro s t X k h hX hk
    simp only [chainOK, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hc, hPQ⟩, hs⟩, hl⟩ := h
    let Pg := mkGL hid hPQ
    have hC : ((Pg * A * Pg⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
        ofCode n c := by
      rw [Units.val_mul, Units.val_mul, val_mkGL, val_inv_mkGL, hA, ← conj_eq hid hc hPQ]
    have hX' : ((X * (Pg * A * Pg⁻¹) : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
        ofCode n s' := by
      rw [Units.val_mul, hX, hC, ofCode_mul_eq hs, hid, Matrix.mul_one]
    obtain ⟨Y, hY, hYt⟩ := ih s' t _ (k + 1) hl hX'
      (Vaserstein.mul_mem_pow_succ hk (Vaserstein.conj_mem_conjugatesOf Pg (IsConj.refl A)))
    exact ⟨Y, by simpa [Nat.add_assoc, Nat.add_comm 1] using hY, hYt⟩

/-- Every pair of nonidentity representatives has a product chain of length `n`. -/
def witOK (n : ℕ) (reps : List ℕ) (idc : ℕ) (wit : List (ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ))) : Bool :=
  allUpTo (fun a => a == 0 || allUpTo (fun b => b == 0 || wit.any (fun e =>
    e.1 == a && e.2.1 == b && e.2.2.length == n &&
      chainOK n (reps.getD a 0) idc idc e.2.2 (reps.getD b 0))) reps.length) reps.length

/-- Each representative has the supplied inverse. -/
def repsOK (n : ℕ) (reps repinv : List ℕ) (idc : ℕ) : Bool :=
  allUpTo (fun r => mulEq n (reps.getD r 0) (repinv.getD r 0) idc idc) reps.length

open Pointwise in
theorem covers_of_certs {n : ℕ} {reps repinv : List ℕ} {idc size : ℕ} {chunks : List ℕ}
    {wit : List (ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ))}
    (hid : ofCode n idc = 1) (h0 : reps.getD 0 0 = idc) (hreps : repsOK n reps repinv idc = true)
    (hscan : scanAll n reps idc size 0 chunks = true) (hwit : witOK n reps idc wit = true) :
    ∀ α g : GL (Fin n) (ZMod 2), α ≠ 1 → g ≠ 1 → g ∈ conjugatesOf α ^ n := by
  have hrep : ∀ r < reps.length, mulEq n (reps.getD r 0) (repinv.getD r 0) idc idc = true :=
    fun r hr => allUpTo_eq_true.1 hreps r hr
  -- every element is conjugate to a representative
  have classify : ∀ g : GL (Fin n) (ZMod 2), ∃ r, ∃ hr : r < reps.length,
      IsConj (mkGL hid (hrep r hr)) g := by
    intro g
    have hg := scanAll_spec chunks 0 hscan (code (g : Matrix (Fin n) (Fin n) (ZMod 2)))
      (Nat.zero_le _) (code_lt _)
    rcases hg with hs | ⟨r, hr, P, Q, hc, hPQ⟩
    · have := det_ofCode_eq_zero hs
      rw [ofCode_code] at this
      exact absurd this (Matrix.GeneralLinearGroup.det_ne_zero g)
    · refine ⟨r, hr, isConj_iff.2 ⟨mkGL hid hPQ, Units.ext ?_⟩⟩
      rw [Units.val_mul, Units.val_mul, val_mkGL, val_inv_mkGL, val_mkGL,
        ← conj_eq hid hc hPQ, ofCode_code]
  have hone : ∀ r (hr : r < reps.length), r = 0 → mkGL hid (hrep r hr) = 1 := by
    rintro r hr rfl
    exact Units.ext (by rw [val_mkGL, h0, hid]; rfl)
  intro α g hα hg
  obtain ⟨a, ha, hαa⟩ := classify α
  obtain ⟨b, hb, hgb⟩ := classify g
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [hone 0 ha rfl, isConj_one_right] at hαa
    exact hα hαa
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [hone 0 hb rfl, isConj_one_right] at hgb
    exact hg hgb
  have h1 := allUpTo_eq_true.1 hwit a ha
  rw [show (a == 0) = false from beq_eq_false_iff_ne.2 ha0, Bool.false_or] at h1
  have h2 := allUpTo_eq_true.1 h1 b hb
  rw [show (b == 0) = false from beq_eq_false_iff_ne.2 hb0, Bool.false_or, List.any_eq_true] at h2
  obtain ⟨e, -, he⟩ := h2
  simp only [Bool.and_eq_true, beq_iff_eq] at he
  obtain ⟨⟨⟨-, -⟩, hlen⟩, hchain⟩ := he
  obtain ⟨Y, hY, hYb⟩ := chainOK_spec hid (mkGL hid (hrep a ha)) (val_mkGL _ _) e.2.2 idc
    (reps.getD b 0) 1 0 hchain (by rw [Units.val_one, hid]) (by simp)
  rw [zero_add, hlen] at hY
  have hYb' : Y = mkGL hid (hrep b hb) := Units.ext (by rw [hYb, val_mkGL])
  obtain ⟨x, rfl⟩ := isConj_iff.1 hgb
  rw [← hYb'] 
  exact Vaserstein.mem_conjugatesOf_pow_of_isConj hαa.symm
    (Vaserstein.conj_mem_conjugatesOf_pow x hY)

end Vaserstein.Bits
