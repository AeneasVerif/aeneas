import Init.Data.List.OfFn

open Lean

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
    simp [Nat.testBit, BitVec.getLsbD]
    cases bv[i] <;> cases b <;> simp [n_pos]
  case isFalse =>
    simp
    if h: j < i then
      simp [h]
    else
      have: j > i := by omega
      simp [this, h]
      cases bv[i] <;> cases b <;> simp [n_pos, (by simp; omega: decide (j - i = 0) = false)]

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


@[simp] theorem BitVec.getElem_ofFn {n} (f: Fin n → Bool) (i: Nat) {i_idx: i < n}
: (BitVec.ofFn f)[i] = f ⟨i, i_idx⟩
:= by simp [ofFn]
