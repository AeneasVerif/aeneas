import Init.Data.List.OfFn
import Init.Data.BitVec.Lemmas
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.BitVec
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Bitwise
import Aeneas.Byte
import Aeneas.Bvify.Init
import Aeneas.SimpLists.SimpLists
import Aeneas.Natify.Natify
import Aeneas.ZModify.ZModify
import Aeneas.List
import Aeneas.SimpScalar
import Aeneas.Grind.Init

open Lean

attribute [-simp] List.getElem!_eq_getElem?_getD

attribute [bvify_simps, simp_scalar_simps] BitVec.zero_eq
attribute [bvify_simps, simp_scalar_simps] BitVec.instInhabited

def BitVec.toArray {n} (bv: BitVec n) : Array Bool := Array.finRange n |>.map (bv[·])
def BitVec.ofFn {n} (f: Fin n → Bool) : BitVec n := (BitVec.ofBoolListLE <| List.ofFn f).cast (by simp)
def BitVec.set {n} (i: Fin n) (b: Bool) (bv: BitVec n) : BitVec n := bv ^^^ (((bv[i] ^^ b).toNat : BitVec n) <<< i.val)

def BitVec.toByteArray {n} (bv: BitVec n) : ByteArray :=
  let paddedLen := (n + 7)/8
  let bv' := bv.setWidth (paddedLen*8)
  ByteArray.mk <| Array.finRange paddedLen
    |>.map fun i =>
      let x := List.finRange 8 |>.map (fun o =>
        2^o.val * if bv'[8*i.val+o.val]'(by omega) then 1 else 0
      ) |>.sum
      UInt8.ofNat x

@[ext]
theorem BitVec.ext {n} {bv1 bv2 : BitVec n}
{point_eq: ∀ i: Nat, (_: i < n) → bv1[i] = bv2[i]}
: bv1 = bv2
:= by
  obtain ⟨⟨a, a_lt⟩⟩ := bv1
  obtain ⟨⟨b, b_lt⟩⟩ := bv2
  simp
  simp [BitVec.getElem_eq_testBit_toNat] at point_eq
  apply Nat.eq_of_testBit_eq
  intro i
  if h: i < n then
    exact point_eq i h
  else
    have: a < 2 ^i := calc
      a < 2 ^n := a_lt
      _ ≤ 2 ^i := Nat.pow_le_pow_of_le Nat.one_lt_two (Nat.le_of_not_gt h)
    simp [Nat.testBit_lt_two_pow this]
    have: b < 2 ^i := calc
      b < 2 ^n := b_lt
      _ ≤ 2 ^i := Nat.pow_le_pow_of_le Nat.one_lt_two (Nat.le_of_not_gt h)
    simp [Nat.testBit_lt_two_pow this]

theorem BitVec.getElem_set {n} {bv: BitVec n} {b: Bool} {i: Fin n} {j: Nat}
:  {j_lt: j < n}
→ (bv.set i b)[j] = if i = j then b else bv[j]
:= by
  intro j_lt
  have n_pos: n > 0 := by cases n <;> (first | cases i.isLt | apply Nat.zero_lt_succ )

  rw [set]
  split
  case isTrue h =>
    subst h
    simp only [Fin.getElem_fin, natCast_eq_ofNat, getElem_xor, getElem_shiftLeft, lt_self_iff_false,
      decide_false, Bool.not_false, tsub_self, Bool.true_and]
    cases bv[i] <;> cases b <;> simp
  case isFalse =>
    simp
    if h: j < i then
      simp only [h, decide_true, Bool.not_true, Bool.false_and, Bool.bne_false]
    else
      have: j > i := by omega
      simp only [h, decide_false, Bool.not_false, Bool.true_and]
      cases bv[i] <;> cases b <;> simp [(by simp; omega: decide (j - i = 0) = false)]

@[simp] theorem BitVec.cast_set {n m} (h: n = m) (bv: BitVec n) (i: Nat) (b: Bool) (i_idx: i < n)
: (bv.set ⟨i, i_idx⟩ b).cast h = (bv.cast h).set ⟨i, h ▸ i_idx⟩ b
:= by subst h; ext; rw [cast_eq, cast_eq]

@[simp] theorem BitVec.getElem_ofBoolListLE {ls: List Bool} {i: Nat}
: ∀ (h: i < ls.length), (BitVec.ofBoolListLE ls)[i] = ls[i]
:= by
  let rec odd_div(x: Nat): (2*x + 1) / 2 = x := by
    cases x
    case zero => simp only [Nat.mul_zero, Nat.zero_add, Nat.reduceDiv]
    case succ =>
      rw [Nat.mul_add, Nat.add_assoc, Nat.add_comm _ 1, ←Nat.add_assoc]
      rw [Nat.add_div_right (H := Nat.two_pos), Nat.add_right_cancel_iff, Nat.add_comm]
      apply odd_div
  intro i_lt
  cases ls
  case nil => contradiction
  case cons hd tl =>
    simp [BitVec.ofBoolListLE, BitVec.getElem_eq_testBit_toNat]
    cases i
    case zero => simp [Nat.mod_eq_of_lt (Bool.toNat_lt hd)]
    case succ i' =>
      have: ((ofBoolListLE tl).toNat * 2 + hd.toNat).testBit (i' + 1) = (ofBoolListLE tl).toNat.testBit i' := by
        cases hd <;> simp [Nat.testBit_succ]; rw [Nat.mul_comm, odd_div]
      simp [this] at i_lt ⊢
      rw [←BitVec.getElem_eq_testBit_toNat (ofBoolListLE tl) i']
      apply BitVec.getElem_ofBoolListLE i_lt
      apply i_lt

@[simp] theorem BitVec.getElem_ofFn {n} (f: Fin n → Bool) (i: Nat) {i_idx: i < n}
: (BitVec.ofFn f)[i] = f ⟨i, i_idx⟩
:= by simp [ofFn]

/-!
# Simp lemmas
-/

attribute [simp, bvify_simps] BitVec.ofNat_mul

theorem BitVec.ofNat_pow {n : ℕ} (x d : ℕ) : BitVec.ofNat n (x ^ d) = (BitVec.ofNat n x)^d := by
  revert x
  induction d <;> simp_all [pow_succ]

@[simp]
theorem BitVec.toNat_pow {w : ℕ} (x : BitVec w) (d : ℕ) :
  BitVec.toNat (x ^ d) = (x.toNat ^ d) % 2^w := by
  induction d <;> simp_all [pow_succ]

@[simp, simp_lists_simps, grind =, agrind =]
theorem BitVec.getElem!_eq_false {w : ℕ} (x : BitVec w) (i : ℕ) (hi : w ≤ i) :
  x[i]! = false := by
  unfold getElem! instGetElem?OfGetElemOfDecidable decidableGetElem?
  simp
  split_ifs <;> simp_all only [not_lt]
  . omega
  . rfl

theorem BitVec.getElem!_eq_getElem {w : ℕ} (x : BitVec w) (i : ℕ) (hi : i < w) :
  x[i]! = x[i] := by
  unfold getElem! instGetElem?OfGetElemOfDecidable decidableGetElem?
  simp only
  split_ifs; simp_all only

@[simp, simp_lists_simps, grind =, agrind =] theorem BitVec.getElem!_or {w} (x y : BitVec w) (i : ℕ) :
  (x ||| y)[i]! = (x[i]! || y[i]!) := by
  -- Simply using the equivalent theorem about `getElem`
  by_cases i < w
  . simp only [getElem!_eq_getElem, getElem_or, *]
  . simp_all only [not_lt, getElem!_eq_false, Bool.or_self]

@[simp, simp_lists_simps, grind =, agrind =] theorem BitVec.getElem!_and {w} (x y : BitVec w) (i : ℕ) :
  (x &&& y)[i]! = (x[i]!&& y[i]!) := by
  -- Simply using the equivalent theorem about `getElem`
  by_cases i < w
  . simp only [getElem!_eq_getElem, getElem_and, *]
  . simp_all only [not_lt, getElem!_eq_false, Bool.and_self]

@[simp, simp_lists_simps]
theorem Bool.toNat_ofNat_mod2 (x : ℕ) : (Bool.ofNat (x % 2)).toNat = x % 2 := by
  have := @Nat.mod_lt x 2 (by simp only [zero_lt_two])
  cases h: x % 2 <;> simp only [ofNat, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, _root_.and_false,
    not_false_eq_true, _root_.decide_true, toNat_true, right_eq_add,
    not_true_eq_false, _root_.decide_false, toNat_false]
  omega

attribute [natify_simps] BitVec.toNat_twoPow

@[simp]
theorem BitVec.twoPow_eq_two_pow {w i} : BitVec.twoPow w i = 2#w ^ i := by
  natify; simp only [toNat_pow, toNat_ofNat]
  by_cases w ≤ 1 <;> cases i <;> simp_scalar

theorem BitVec.getElem!_eq_testBit_toNat {w : ℕ} (x : BitVec w) (i : ℕ) :
  x[i]! = x.toNat.testBit i := by
  by_cases i < w
  . have : x[i]! = x[i] := by
      simp only [getElem!_eq_getElem, *]
    rw [this]
    simp only [getElem_eq_testBit_toNat]
  . simp_all only [not_lt, getElem!_eq_false, Bool.false_eq]
    have : x.toNat < 2^w := by omega
    apply Nat.testBit_eq_false_of_lt
    have : 2^w ≤ 2^i := by apply Nat.pow_le_pow_right <;> omega
    omega

@[simp]
theorem BitVec.and_two_pow_sub_one_eq_mod {w} (x : BitVec w) (n : Nat) :
  x &&& 2#w ^ n - 1#w = x % 2#w ^ n := by
  by_cases hn : n < w
  . simp only [← ofNat_pow]
    natify
    simp
    have : 2^n < 2^w := by
      apply Nat.pow_lt_pow_of_lt <;> omega
    -- TODO: simp_arith
    simp (disch := omega) only [Nat.one_mod_two_pow, Nat.mod_eq_of_lt]
    have : 1 ≤ 2^n := by
      have : 2^0 ≤ 2^n := by apply Nat.pow_le_pow_of_le <;> omega
      omega
    have : 2 ^ w - 1 + 2 ^ n = 2^w + (2^n - 1) := by omega
    rw [this]
    simp (disch := omega) only [Nat.add_mod_left, Nat.mod_eq_of_lt, Nat.and_two_pow_sub_one_eq_mod]
  . simp only [← ofNat_pow]
    simp only [not_lt] at hn
    have : BitVec.ofNat w (2 ^ n) = 0 := by
      unfold BitVec.ofNat Fin.Internal.ofNat
      have : 2^n % 2^w = 0 := by
        have : n = w + (n - w) := by omega
        rw [this, Nat.pow_add]
        simp only [Nat.mul_mod_right]
      simp only [this]
      rfl
    rw [this]
    simp only [ofNat_eq_ofNat, BitVec.zero_sub, umod_zero]
    natify
    simp only [toNat_neg, toNat_ofNat]
    by_cases hw: 0 < w
    . have : (2 ^ w - 1 % 2 ^ w) % 2 ^ w = 2^w - 1 := by
        have hLt : 1 < 2^w := by
          have : 2^0 < 2^w := by -- TODO: scalar_tac +nonLin
            apply Nat.pow_lt_pow_of_lt <;> omega
          omega
        have : (2^w - 1) % 2^w = 2^w - 1 := by apply Nat.mod_eq_of_lt; omega
        rw [← this]
        zmodify
      simp only [this, Nat.and_two_pow_sub_one_eq_mod, toNat_mod_cancel]
    . have : x.toNat < 2^w := by omega
      simp_all only [ofNat_eq_ofNat, not_lt, nonpos_iff_eq_zero, pow_zero, Nat.lt_one_iff,
        Nat.mod_self, tsub_zero, Nat.and_self]

@[simp, simp_lists_simps, simp_scalar_simps, grind =, agrind =]
theorem BitVec.shiftLeft_sub_one_eq_mod {w} (x : BitVec w) (n : Nat) :
  x &&& 1#w <<< n - 1#w = x % 2 ^ n := by
  simp only [BitVec.ofNat_eq_ofNat]
  simp only [BitVec.shiftLeft_eq_mul_twoPow]
  have : 1#w * BitVec.twoPow w n = 2#w ^ n := by
    have : 1#w = 1 := by simp
    rw [this]
    ring_nf
    natify; simp only [toNat_pow, BitVec.toNat_ofNat]
    zmodify
  rw [this]
  simp only [BitVec.and_two_pow_sub_one_eq_mod]

@[simp, simp_lists_simps, grind =, agrind =]
theorem BitVec.getElem!_zero (w i : ℕ ) : (0#w)[i]! = false := by
  simp only [getElem!_eq_testBit_toNat, toNat_ofNat, Nat.zero_mod, Nat.zero_testBit]

@[simp, simp_lists_simps, grind =, agrind =]
theorem BitVec.getElem!_shiftLeft_false {w} (v : BitVec w) (n i : ℕ) (h : i < n ∨ w ≤ i) :
  (v <<< n)[i]! = false := by
  simp only [getElem!_eq_testBit_toNat, toNat_shiftLeft, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft, ge_iff_le, Bool.and_eq_false_imp, decide_eq_true_eq]
  omega

@[simp, simp_lists_simps, grind =, agrind =]
theorem BitVec.getElem!_shiftLeft_eq {w} (v : BitVec w) (n i : ℕ) (h : n ≤ i ∧ i < w) :
  (v <<< n)[i]! = v[i - n]! := by
  simp only [getElem!_eq_testBit_toNat, toNat_shiftLeft, Nat.testBit_mod_two_pow, h, decide_true,
    Nat.testBit_shiftLeft, Bool.true_and]

@[simp, simp_lists_simps, grind =, agrind =]
theorem BitVec.getElem!_shiftRight {w} (v : BitVec w) (n i : ℕ) :
  (v >>> n)[i]! = v[n + i]! := by
  simp only [getElem!_eq_testBit_toNat, toNat_ushiftRight, Nat.testBit_shiftRight]

@[simp, simp_lists_simps, grind =, agrind =]
theorem BitVec.getElem!_mod_pow2_eq {w} (x : BitVec w) (i j : ℕ) (h : j < i) :
  (x % 2#w ^ i)[j]! = x[j]! := by
  simp [BitVec.getElem!_eq_testBit_toNat]
  by_cases hw : w = 0
  . simp_all only [pow_zero]
    cases i <;> simp_all
  . -- TODO: scalar_tac +nonLin
    by_cases hw: w = 1
    . simp_all only [one_ne_zero, not_false_eq_true, pow_one, Nat.mod_self]
      cases i <;> simp_all only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        zero_pow, Nat.zero_mod, Nat.mod_zero, not_lt_zero']
    . have : 2 < 2^w := by
        have : 2^1 < 2^w := by apply Nat.pow_lt_pow_of_lt <;> omega
        omega
      simp (disch := omega) only [Nat.mod_eq_of_lt]
      by_cases hi: i < w
      . -- TODO: scalar_tac +nonLin
        have : 2^i < 2^w := by
          apply Nat.pow_lt_pow_of_lt <;> omega
        simp (disch := omega) only [Nat.mod_eq_of_lt, Nat.testBit_mod_two_pow,
          Bool.and_eq_right_iff_imp, decide_eq_true_eq]
        omega
      . -- TODO: scalar_tac +nonLin
        have : 2^i % 2^w = 0 := by
          have : i = w + (i - w) := by omega
          rw [this]
          simp only [Nat.pow_add, Nat.mul_mod_right]
        simp only [this, Nat.mod_zero]

@[simp, simp_lists_simps, grind =, agrind =]
theorem BitVec.getElem!_mod_pow2_false {w} (x : BitVec w) (i j : ℕ) (h : i ≤ j) :
  (x % 2#w ^ i)[j]! = false := by
  simp [BitVec.getElem!_eq_testBit_toNat]
  have : x.toNat < 2^w := by omega
  by_cases hw: w ≤ 1
  . have hw : w = 0 ∨ w = 1 := by omega
    cases hw <;> simp_all only [pow_zero, Nat.lt_one_iff, zero_le, Nat.zero_mod,
                                Nat.zero_testBit, pow_one, le_refl, Nat.mod_self]
    cases i <;> simp_all only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
                               zero_pow, Nat.zero_mod, Nat.mod_zero, zero_le, pow_zero, Nat.mod_succ,
                               Nat.mod_one, Nat.zero_testBit]
    apply Nat.testBit_eq_false_of_lt
    -- TODO: scalar_tac +nonLin
    have : 2^1 ≤ 2^j := by apply Nat.pow_le_pow_of_le <;> omega
    omega
  . -- TODO: scalar_tac +nonLin
    have : 2^1 < 2^w := by apply Nat.pow_lt_pow_of_lt <;> omega
    simp (disch := omega) only [Nat.mod_eq_of_lt]
    by_cases hi: i < w
    . -- TODO: scalar_tac +nonLin
      have : 2^i < 2^w := by apply Nat.pow_lt_pow_of_lt <;> omega
      simp (disch := omega) only [Nat.mod_eq_of_lt, Nat.testBit_mod_two_pow,
                                  Bool.and_eq_false_imp, decide_eq_true_eq]
      omega
    . -- TODO: scalar_tac +nonLin
      have : 2^i % 2^w = 0 := by
        have : i = w + (i - w) := by omega
        rw [this]
        simp only [Nat.pow_add, Nat.mul_mod_right]
      simp only [this, Nat.mod_zero]
      have : w ≤ j := by omega
      apply Nat.testBit_eq_false_of_lt
      -- TODO: scalar_tac +nonLin
      have : 2^w ≤ 2^j := by apply Nat.pow_le_pow_of_le <;> omega
      omega

@[simp_lists_simps, grind =, agrind =]
theorem BitVec.getElem!_toNat_eq_false {n} (b : BitVec n) (i : ℕ) (hi : n ≤ i) :
  b.toNat.testBit i = false := by
  rw [← BitVec.getElem!_eq_testBit_toNat]
  simp_lists

theorem BitVec.eq_iff {n} (b0 b1 : BitVec n) : b0 = b1 ↔ ∀ i < n, b0[i]! = b1[i]! := by
  constructor
  . simp +contextual
  . intro h
    apply BitVec.eq_of_toNat_eq
    apply Nat.eq_of_testBit_eq
    intros i
    simp [BitVec.getElem!_eq_testBit_toNat] at h
    by_cases hi : i < n
    . simp_lists [h]
    . simp_lists

theorem Byte.eq_iff (b0 b1 : Byte) : b0 = b1 ↔ ∀ i < 8, b0.testBit i = b1.testBit i := by
  constructor
  . simp +contextual
  . intro h
    rw [BitVec.eq_iff]
    simp_lists [BitVec.getElem!_eq_testBit_toNat, h]

/-!
# Conversion to a little/big-endian list of bytes
-/

def BitVec.toLEBytes {w : ℕ} (b : BitVec w) : List Byte :=
  if w > 0 then
    b.setWidth 8 :: BitVec.toLEBytes ((b >>> 8).setWidth (w - 8))
  else []

def BitVec.toBEBytes {w : ℕ} (b : BitVec w) : List Byte :=
  List.reverse b.toLEBytes

def BitVec.fromLEBytes (l : List Byte) : BitVec (8 * l.length) :=
  match l with
  | [] => BitVec.ofNat _ 0
  | b :: l =>
    BitVec.setWidth (8 * (b :: l).length) b ||| ((BitVec.fromLEBytes l).setWidth (8 * (b :: l).length) <<< 8)

def BitVec.fromBEBytes (l : List Byte) : BitVec (8 * l.length) :=
  (BitVec.fromLEBytes l.reverse).cast (by simp)

@[simp, simp_lists_simps, simp_scalar_simps, grind =, agrind =]
theorem BitVec.toLEBytes_length {w} (v : BitVec w) (h : w % 8 = 0) :
  v.toLEBytes.length = w / 8 := by
  if h1: w = 0 then
    simp only [toLEBytes, gt_iff_lt, lt_self_iff_false, ↓reduceIte, List.length_nil, Nat.zero_div,
      h1]
  else
    unfold toLEBytes
    have : w > 0 := by omega
    simp only [gt_iff_lt, ↓reduceIte, List.length_cons, this]
    rw [BitVec.toLEBytes_length]
    . have : w ≥ 8 := by omega
      have : w = (w  - 8) + 8 := by omega
      conv => rhs; rw [this]
      simp only [Nat.ofNat_pos, Nat.add_div_right]
    . omega

@[simp, simp_lists_simps, grind =, agrind =]
theorem BitVec.getElem!_cast (x : BitVec n) (h : n = m) (i : ℕ) :
  (x.cast h)[i]! = x[i]! := by
  simp only [getElem!_eq_testBit_toNat, toNat_cast]

-- TODO: move
@[simp_lists_simps, grind =, agrind =]
theorem List.getElem!_cons_eq_getElem!_sub {α} [Inhabited α] (x : α) (tl : List α) (i : ℕ) (hi : 0 < i) :
  (x :: tl)[i]! = tl[i - 1]! := by
  simp only [Nat.not_eq, ne_eq, not_lt_zero', or_true, getElem!_cons_nzero, hi]

@[simp_lists_simps, grind =, agrind =]
theorem List.getElem!_cons_zero' {α} [Inhabited α] (x : α) (tl : List α) (i : ℕ) (hi : i = 0) :
  (x :: tl)[i]! = x := by
  simp only [hi, getElem!_cons_zero]

@[simp, simp_lists_simps, grind =, agrind =]
theorem BitVec.toLEBytes_getElem!_testBit (v : BitVec w) (i j : ℕ) (hj : j < 8) :
  (v.toLEBytes[i]!).testBit j = v[8 * i + j]! := by
  unfold toLEBytes
  split
  . by_cases hi: i = 0 <;> simp_lists
    . simp only [MulZeroClass.mul_zero, zero_add, hi]
      simp only [Byte.testBit, toNat_setWidth, Nat.reducePow, getElem!_eq_testBit_toNat]
      have : 256 = 2^8 := by simp only [Nat.reducePow]
      simp only [this, Nat.testBit_mod_two_pow]
      simp only [decide_true, Bool.true_and, hj]
    . have := BitVec.toLEBytes_getElem!_testBit (setWidth (w - 8) (v >>> 8)) (i - 1) j hj
      simp only [this]
      simp only [getElem!_eq_testBit_toNat, toNat_setWidth, toNat_ushiftRight,
        Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
      have : 8 + (8 * (i - 1) + j) = 8 * i + j := by omega
      simp only [this, Bool.and_eq_right_iff_imp, decide_eq_true_eq]
      by_cases 8 * i + j < w
      . omega
      . simp_lists
  . simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero, List.length_nil, zero_le,
    List.getElem!_default, Byte.testBit_default, Bool.false_eq] at *
    simp_lists
termination_by i

@[simp, simp_lists_simps, grind =, agrind =]
theorem BitVec.fromLEBytes_getElem! (v : List Byte) (j : ℕ) :
  (BitVec.fromLEBytes v)[j]! = v[j / 8]!.testBit (j % 8) := by
  unfold BitVec.fromLEBytes
  match hv: v with
  | [] => simp only [List.length_nil, Nat.mul_zero, zero_le, getElem!_eq_false,
    List.getElem!_default, Byte.testBit_default]
  | x :: v' =>
    simp only [List.length_cons, getElem!_or]
    by_cases hj: j < 8
    . have : j < 8 * (v'.length + 1) := by scalar_tac
      simp_lists
      simp only [getElem!_eq_testBit_toNat, toNat_setWidth, Nat.testBit_mod_two_pow, decide_true,
        Bool.true_and, this]
      have : j % 8 = j := by apply Nat.mod_eq_of_lt; omega
      simp only [this]
    . have : 0 < j / 8 := by scalar_tac +nonLin
      simp_lists
      simp only [getElem!_eq_testBit_toNat, toNat_setWidth, Nat.testBit_mod_two_pow,
        toNat_shiftLeft, Nat.ofNat_pos, mul_lt_mul_iff_right₀, lt_add_iff_pos_right, Nat.lt_one_iff,
        pos_of_gt, toNat_mod_cancel_of_lt, Nat.testBit_shiftLeft, ge_iff_le]
      have : 8 ≤ j := by omega
      simp only [this, decide_true, Bool.true_and]
      have := BitVec.fromLEBytes_getElem! v' (j - 8)
      simp only [getElem!_eq_testBit_toNat] at this
      simp only [this]
      simp_lists
      by_cases hj': j < 8 * (v'.length + 1)
      . simp [hj']
        have h0 : (j - 8) / 8 = (j / 8) - 1 := by omega
        have h1 : (j - 8) % 8 = j % 8 := by omega
        simp only [h0, h1]
      . simp_lists

@[simp, simp_lists_simps, grind =, agrind =]
theorem BitVec.fromLEBytes_toLEBytes {w : ℕ} (h : w % 8 = 0) (b : BitVec w) :
  BitVec.fromLEBytes b.toLEBytes = BitVec.cast (by simp only [toLEBytes_length, Nat.dvd_iff_mod_eq_zero, Nat.mul_div_cancel', h]) b := by
  simp only [eq_iff, fromLEBytes_getElem!, getElem!_cast]
  simp_lists
  simp only [Nat.dvd_iff_mod_eq_zero, h, Nat.mul_div_cancel']
  simp only [Nat.div_add_mod, implies_true]

@[simp]
theorem BitVec.toBEBytes_length {w} (v : BitVec w) (h : w % 8 = 0) :
  v.toBEBytes.length = w / 8 := by
  unfold toBEBytes
  simp only [List.length_reverse, toLEBytes_length, h]

@[simp, simp_lists_simps, grind =, agrind =]
theorem BitVec.getElem!_default_eq_false {w} (i : ℕ) :
  (default : BitVec w)[i]! = false := by simp only [default, zero_eq, getElem!_zero]

@[simp, simp_lists_simps, grind =, agrind =]
theorem BitVec.getElem!_setWidth {n : Nat} (m : Nat) (x : BitVec n) (i : Nat) (h : i < m) :
  (setWidth m x)[i]! = x[i]! := by
  simp only [getElem!_eq_testBit_toNat, toNat_setWidth, Nat.testBit_mod_two_pow,
    Bool.and_eq_right_iff_imp, decide_eq_true_eq]
  omega

@[simp, simp_lists_simps, grind =, agrind =]
theorem BitVec.getElem!_setWidth_eq_false {n : Nat} (m : Nat) (x : BitVec n)
  (i : Nat) (h : n ≤ i ∨ m ≤ i) :
  (setWidth m x)[i]! = false := by
  simp only [getElem!_eq_testBit_toNat, toNat_setWidth, Nat.testBit_mod_two_pow,
    Bool.and_eq_false_imp, decide_eq_true_eq]
  cases h <;> try omega
  intros
  have : x[i]! = false := by simp_lists
  simp only [getElem!_eq_testBit_toNat] at this
  apply this

@[simp, simp_lists_simps, grind =, agrind =]
theorem BitVec.getElem!_toLEBytes {w : ℕ} (b : BitVec w) (i j : ℕ) (h : j < 8) :
  (b.toLEBytes[i]!)[j]! = b[8 * i + j]! := by
  if h1: w = 0 then
    simp_all only [Nat.zero_mod, toLEBytes_length, Nat.zero_div, not_lt_zero', not_false_eq_true,
      getElem!_neg, getElem!_pos, Bool.default_bool]
    simp only [default, zero_eq, getElem_zero]
  else
    unfold toLEBytes
    have : w > 0 := by omega
    simp only [gt_iff_lt, this, ↓reduceIte]
    by_cases hi: i = 0
    . simp_all only [gt_iff_lt, List.getElem!_cons_zero, getElem!_setWidth, MulZeroClass.mul_zero,
      zero_add]
    . simp only [Nat.not_eq, ne_eq, hi, not_false_eq_true, not_lt_zero', false_or, true_or,
      List.getElem!_cons_nzero]
      rw [getElem!_toLEBytes]
      . by_cases 8 * i + j < w
        . have : 8 * (i - 1) + j < w - 8 := by omega
          simp only [getElem!_setWidth, getElem!_shiftRight, this]
          congr 1; omega
        . simp_lists
      . omega

@[simp, simp_lists_simps, grind =, agrind =]
theorem BitVec.testBit_getElem!_toLEBytes {w:ℕ} (x : BitVec w) (i j : ℕ) (h : j < 8) :
  x.toLEBytes[i]!.testBit j = x[8 * i + j]! := by
  have := getElem!_toLEBytes x i j h
  simp_all only [List.getElem!_eq_getElem?_getD, getElem!_eq_testBit_toNat]

theorem BitVec.or_mod_two_pow {n : Nat} (a b : BitVec n) (k : Nat) :
  (a ||| b) % 2 ^ k = (a % 2 ^ k) ||| (b % 2 ^ k) := by
  by_cases k < n <;> natify <;> simp
  · have : 2 ^ k < 2 ^ n := by simp_scalar
    cases k
    · simp; simp_scalar; rfl
    · rename_i k _
      simp_scalar
  · by_cases hn : n ≤ 1
    · have : n = 0 ∨ n = 1 := by omega
      cases this <;> simp [*, Nat.mod_one]
      simp_scalar
    · simp_scalar

@[simp]
theorem BitVec.or_mod_two_pow_iff_true {n : Nat} (a b : BitVec n) (k : Nat) :
  ((a ||| b) % 2 ^ k = (a % 2 ^ k) ||| (b % 2 ^ k)) ↔ True := by
  simp only [BitVec.or_mod_two_pow]

@[simp]
theorem BitVec.or_mod_two_pow_iff_true' {n : Nat} (a b : BitVec n) (k : Nat) :
  ((a % 2 ^ k) ||| (b % 2 ^ k) = (a ||| b) % 2 ^ k) ↔ True := by
  simp only [BitVec.or_mod_two_pow]

theorem BitVec.and_mod_two_pow {n : Nat} (a b : BitVec n) (k : Nat) :
  (a &&& b) % 2 ^ k = (a % 2 ^ k) &&& (b % 2 ^ k) := by
  by_cases k < n <;> natify <;> simp
  · have : 2 ^ k < 2 ^ n := by simp_scalar
    cases k
    · simp; simp_scalar; rfl
    · rename_i k _
      simp_scalar
  · by_cases hn : n ≤ 1
    · have : n = 0 ∨ n = 1 := by omega
      cases this <;> simp [*, Nat.mod_one]
      simp_scalar
    · simp_scalar

@[simp]
theorem BitVec.and_mod_two_pow_iff_true {n : Nat} (a b : BitVec n) (k : Nat) :
  ((a &&& b) % 2 ^ k = (a % 2 ^ k) &&& (b % 2 ^ k)) ↔ True := by
  simp only [BitVec.and_mod_two_pow]

@[simp]
theorem BitVec.and_mod_two_pow_iff_true' {n : Nat} (a b : BitVec n) (k : Nat) :
  ((a % 2 ^ k) &&& (b % 2 ^ k) = (a &&& b) % 2 ^ k) ↔ True := by
  simp only [BitVec.and_mod_two_pow]

theorem BitVec.xor_mod_two_pow {n : Nat} (a b : BitVec n) (k : Nat) :
  (a ^^^ b) % 2 ^ k = (a % 2 ^ k) ^^^ (b % 2 ^ k) := by
  by_cases k < n <;> natify <;> simp
  · have : 2 ^ k < 2 ^ n := by simp_scalar
    cases k
    · simp; simp_scalar; rfl
    · rename_i k _
      simp_scalar
  · by_cases hn : n ≤ 1
    · have : n = 0 ∨ n = 1 := by omega
      cases this <;> simp [*, Nat.mod_one]
      simp_scalar
    · simp_scalar

@[simp]
theorem BitVec.xor_mod_two_pow_iff_true {n : Nat} (a b : BitVec n) (k : Nat) :
  ((a ^^^ b) % 2 ^ k = (a % 2 ^ k) ^^^ (b % 2 ^ k)) ↔ True := by
  simp only [BitVec.xor_mod_two_pow]

@[simp]
theorem BitVec.xor_mod_two_pow_iff_true' {n : Nat} (a b : BitVec n) (k : Nat) :
  ((a % 2 ^ k) ^^^ (b % 2 ^ k) = (a ^^^ b) % 2 ^ k) ↔ True := by
  simp only [BitVec.xor_mod_two_pow]

@[simp, simp_lists_simps, simp_scalar_simps]
theorem BitVec.ofNat_shiftRight_toNat {n m} (bv : BitVec n) (i : Nat) :
  (BitVec.ofNat m (bv.toNat >>> i)) = BitVec.setWidth m (bv >>> i) := by
  natify; simp

@[simp, simp_lists_simps, simp_scalar_simps]
theorem BitVec.cast_shiftRight_toNat {n m} (bv : BitVec n) (i : Nat) :
  ((bv.toNat >>> i) : BitVec m) = BitVec.setWidth m (bv >>> i) := by
  natify; simp

@[simp, simp_lists_simps, simp_scalar_simps]
theorem BitVec.ofNat_shiftLeft_toNat {n m} (bv : BitVec n) (i : Nat) (h : m ≤ n) :
  (BitVec.ofNat m (bv.toNat <<< i)) = BitVec.setWidth m (bv <<< i) := by
  natify; simp; simp_scalar

@[simp, simp_lists_simps, simp_scalar_simps]
theorem BitVec.cast_shiftLeft_toNat {n m} (bv : BitVec n) (i : Nat) (h : m ≤ n) :
  ((bv.toNat <<< i) : BitVec m) = BitVec.setWidth m (bv <<< i) := by
  natify; simp; simp_scalar
