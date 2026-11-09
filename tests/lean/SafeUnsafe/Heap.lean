import SafeUnsafe.SafeUnsafe

/-! Running the closed programs of `SafeUnsafe` on the byte heap, one effect at a time, from the
empty heap: the allocations are given an explicit placement (otherwise the run could end with
`oom`, which every specification allows), the checked operations either fail (`undef`, which no
specification allows) or have a successor, and a program is UB when some reachable operation has
no successor. -/

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Aeneas.Data.Coinductive

unseal Result

namespace Aeneas.Data.Coinductive

variable {α β : Type} {Q : effectWP.Post β} {s : Heap}

theorem DWP.heap_choose {modify : State → α → State → Prop} {k : ULift α → Result β}
    (hSpec : DWP effectWP (Result.vis (.guardedModify α modify) k) Q s)
    (x : α) (s' : Heap) (hx : modify s x s') : DWP effectWP (k ⟨x⟩) Q s' :=
  hSpec.vis_view.2 x s' hx

theorem DWP.heap_fail {e : Error} {k : RustEffect.Output (RustEffect.Input.fail e) → Result β}
    (hSpec : DWP effectWP (Result.vis (.fail e) k) Q s) (he : e ≠ .oom := by simp) : False :=
  he hSpec.vis_view

/-- A checked operation either fails, or has a successor. -/
theorem DWP.heap_checked {modify : State → α → State → Prop} {k : ULift (Option α) → Result β}
    (hSpec : DWP effectWP (Result.vis (.guardedModify (Option α) (State.checked modify)) k) Q s)
    (hNone : DWP effectWP (k ⟨none⟩) Q s → False) :
    ∃ v s', modify s v s' ∧ DWP effectWP (k ⟨some v⟩) Q s' := by
  obtain ⟨⟨x, s', hx⟩, hAll⟩ := hSpec.vis_view
  cases x with
  | none =>
    obtain ⟨hn, rfl⟩ := hx
    exact (hNone (hAll none _ ⟨hn, rfl⟩)).elim
  | some v => exact ⟨v, s', hx, hAll (some v) s' hx⟩

/-- A checked operation with no successor fails. -/
theorem DWP.heap_stuck {modify : State → α → State → Prop} {k : ULift (Option α) → Result β}
    (hSpec : DWP effectWP (Result.vis (.guardedModify (Option α) (State.checked modify)) k) Q s)
    (hNone : DWP effectWP (k ⟨none⟩) Q s → False) (hStuck : ¬ ∃ v s', modify s v s') : False :=
  hNone (hSpec.heap_choose none s ⟨hStuck, rfl⟩)

end Aeneas.Data.Coinductive

namespace safe_unsafe.Heap

theorem pow_numBits_gt : 2^32 ≤ 2^System.Platform.numBits := by
  rcases System.Platform.numBits_eq with h | h <;> simp [h]

/-- A closed program runs from the empty heap. -/
theorem dwp_empty {m : Result α} {Q : IPost α} (hTriple : ispec emp m Q) :
    DWP effectWP m (fun value s' => Realizes ((Q ∗+ emp) value) s') Heap.empty :=
  ispec_iff.mp hTriple emp Heap.empty (realizes_sep_emp.mpr realizes_emp_empty)

/-- The encoding of a `u32`. -/
def enc (v : U32) : Vector Std.Byte (Pointee.repr (T := U32)).size :=
  ⟨(v.bv.toLEBytes.map (Std.Byte.data ∘ UScalar.mk)).toArray, by simp; rfl⟩

@[simp] theorem enc_getElem (v : U32) (i : Nat) (h : i < (Pointee.repr (T := U32)).size) :
    (enc v)[i] = .data ⟨v.bv.toLEBytes[i]'(by
      have : (Pointee.repr (T := U32)).size = 4 := rfl
      simp; omega)⟩ := by
  simp [enc]

@[simp] theorem enc_toList_length (v : U32) : (enc v).toList.length = 4 := by
  simp; rfl

theorem encode_enc (v : U32) : (Pointee.repr (T := U32)).encode v (enc v) := by
  show (enc v).toList = _
  simp only [enc, Vector.toList, List.map_map]

theorem encodeList_enc (vs : List U32) : (Pointee.repr (T := U32)).encodeList vs (vs.map enc) := by
  induction vs with
  | nil => simp [Repr.encodeList]
  | cons v vs ih => exact ⟨encode_enc v, ih⟩

theorem exposes_of_encode {T : Type} {repr : Std.Repr T} {v : T} {data : Vector Std.Byte repr.size}
    (h : repr.encode v data) (s : State) (address : Nat) : State.exposes repr s address v data := by
  refine ⟨repr.encode_decode _ _ h, fun i => ?_⟩
  split
  · next p lane hb => exact Or.inl ⟨data, h, i, lane, hb⟩
  · trivial

theorem exposesList_enc (s : State) (address : Nat) (vs : List U32) :
    State.exposesList Pointee.repr s address vs (vs.map enc) := by
  induction vs generalizing address with
  | nil => simp [State.exposesList]
  | cons v vs ih => exact ⟨exposes_of_encode (encode_enc v) s address, ih _⟩

theorem usize_mk_val (n : Nat) (h : n < 2^32) :
    (UScalar.mk (BitVec.ofNat System.Platform.numBits n) : Usize).val = n := by
  have := pow_numBits_gt
  show (BitVec.ofNat System.Platform.numBits n).toNat = n
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

@[simp] theorem create_cons_enc_length (v : U32) (data : List (Vector Std.Byte _)) (depth : Nat) :
    ((Pointee.repr (T := U32)).create (enc v :: data) depth).length =
      4 + ((Pointee.repr (T := U32)).create data depth).length := by
  simp [Std.Repr.create]; rfl

@[simp] theorem create_nil_length (depth : Nat) :
    ((Pointee.repr (T := U32)).create [] depth).length = 0 := by
  simp [Std.Repr.create]

theorem create_enc_length (vs : List U32) (depth : Nat) :
    ((Pointee.repr (T := U32)).create (vs.map enc) depth).length = 4 * vs.length := by
  induction vs with
  | nil => simp [Std.Repr.create]
  | cons v vs ih =>
    simp only [Std.Repr.create, List.map_cons, List.flatMap_cons, List.length_append,
      List.length_map, enc_toList_length, List.length_cons] at ih ⊢
    omega

/-- The block of the values `vs` at `b`, shared `depth` times. -/
def block (b : Usize) (root : Nat) (vs : List U32) (owned : Bool) (depth : Nat) : Block :=
  ⟨b, root, (Pointee.repr (T := U32)).create (vs.map enc) depth, owned, true, true⟩

/-- The heap with a new block. -/
def add (s : Heap) (blk : Block) : Heap := ⟨update s.allocations s.next (some blk), s.next + 1⟩

theorem align_u32 : (Pointee.repr (T := U32)).align.val = 4 := rfl

theorem size_u32 : (Pointee.repr (T := U32)).size = 4 := rfl

/-- Allocation (`into_raw`, `from_mut`, `as_mut_ptr`), at the placement `b`. -/
theorem _root_.Aeneas.Data.Coinductive.DWP.heap_newBlock {β : Type} {Q : effectWP.Post β} {s : Heap} {vs : List U32} {own : Bool}
    {k : ULift (Option (RawPtr U32)) → Result β}
    (hSpec : DWP effectWP (Result.vis (.guardedModify (Option (RawPtr U32))
      (State.checked (State.newBlock Pointee.repr vs own))) k) Q s)
    (b : Usize) (hAlign : 4 ∣ b.val) (hFresh : s.allocations s.next = none)
    (hCheck : (add s (block b s.next vs own 0)).check = true) :
    DWP effectWP (k ⟨some ⟨s.next, b⟩⟩) Q (add s (block b s.next vs own 0)) := by
  refine hSpec.heap_choose _ _ ⟨vs.map enc, b, none, ?_, ?_⟩
  · cases own
    · exact exposesList_enc s b.val vs
    · exact encodeList_enc vs
  · simp only [Heap.newBlock, align_u32, Heap.createRepr, hFresh]
    simp [hAlign, Heap.commit, add, block, hCheck] at *

/-- Allocation or exposure of values of any representation, with their encodings `data`, at `b`. -/
theorem _root_.Aeneas.Data.Coinductive.DWP.heap_newBlock_data {T β : Type} {Q : effectWP.Post β}
    {s : Heap} {repr : Std.Repr T} {vs : List T} {own : Bool}
    {k : ULift (Option (RawPtr T)) → Result β}
    (hSpec : DWP effectWP (Result.vis (.guardedModify (Option (RawPtr T))
      (State.checked (State.newBlock repr vs own))) k) Q s)
    (data : List (Vector Std.Byte repr.size)) (b : Usize)
    (hData : if own then repr.encodeList vs data else State.exposesList repr s b.val vs data)
    (hAlign : repr.align.val ∣ b.val) (hFresh : s.allocations s.next = none)
    (hCheck : (add s ⟨b, s.next, repr.create data 0, own, true, true⟩).check = true) :
    DWP effectWP (k ⟨some ⟨s.next, b⟩⟩) Q (add s ⟨b, s.next, repr.create data 0, own, true, true⟩) := by
  refine hSpec.heap_choose _ _ ⟨data, b, none, hData, ?_⟩
  simp only [Heap.newBlock, Heap.createRepr, hFresh]
  simp [hAlign, Heap.commit, add, hCheck] at *

/-- Shared exposure (`as_ptr`), at the placement `b`. -/
theorem _root_.Aeneas.Data.Coinductive.DWP.heap_newSharedExposure {β : Type} {Q : effectWP.Post β} {s : Heap} {vs : List U32}
    {k : ULift (Option (RawPtr U32)) → Result β}
    (hSpec : DWP effectWP (Result.vis (.guardedModify (Option (RawPtr U32))
      (State.checked (State.newSharedExposure Pointee.repr vs))) k) Q s)
    (b : Usize) (hAlign : 4 ∣ b.val) (hFresh : s.allocations s.next = none)
    (hCheck : (add s (block b s.next vs false 1)).check = true) :
    DWP effectWP (k ⟨some ⟨s.next, b⟩⟩) Q (add s (block b s.next vs false 1)) := by
  refine hSpec.heap_choose _ _ ⟨vs.map enc, b, none, exposesList_enc s b.val vs, ?_⟩
  simp only [Heap.newSharedExposure, align_u32, Heap.createRepr, hFresh]
  simp [hAlign, Heap.commit, add, block, hCheck] at *

end safe_unsafe.Heap

namespace safe_unsafe.Heap

open Aeneas.Std

/-! The successors of the checked operations. -/

theorem removeExposure_eq {T : Type} {repr : Std.Repr T} {p : RawPtr T} {n : Nat} {s s' : Heap}
    {u : Unit} (h : State.removeExposure repr p n s u s') : s' = s.retire p.provenance := by
  simp only [State.removeExposure, Heap.endExposureAt] at h
  cases hb : s.allocations p.provenance <;> simp only [hb, Option.bind_eq_bind, Option.bind_none,
    Option.bind_some, reduceCtorEq] at h
  split at h
  · exact (Heap.commit_success _ _ h).1
  · contradiction

theorem returnOwned_eq {T : Type} {repr : Std.Repr T} {p : RawPtr T} {n : Nat} {s s' : Heap}
    {u : Unit} (h : State.returnOwned repr p n s u s') : s' = s.retire p.provenance := by
  simp only [State.returnOwned, Heap.returnOwned] at h
  cases hb : s.allocations p.provenance <;> simp only [hb, Option.bind_eq_bind, Option.bind_none,
    Option.bind_some, reduceCtorEq] at h
  next blk =>
  cases hr : s.allocations blk.root <;> simp only [hr, Option.bind_none, Option.bind_some,
    reduceCtorEq] at h
  split at h
  · exact (Heap.commit_success _ _ h).1
  · contradiction

theorem endSharedExposure_eq {T : Type} {repr : Std.Repr T} {p : RawPtr T} {vs : List T}
    {s s' : Heap} {u : Unit} (h : State.endSharedExposure repr p vs s u s') :
    s' = s.retire p.provenance := by
  obtain ⟨-, h⟩ := h
  simp only [Heap.endSharedExposure, Heap.endExposureAt] at h
  cases hb : s.allocations p.provenance <;> simp only [hb, Option.bind_eq_bind, Option.bind_none,
    Option.bind_some, reduceCtorEq] at h
  split at h
  · exact (Heap.commit_success _ _ h).1
  · contradiction

theorem read_eq {T : Type} {repr : Std.Repr T} {p : RawPtr T} {s s' : Heap} {v : T}
    (h : State.read repr p s v s') : s' = s := h.2

theorem offset_eq {T : Type} {repr : Std.Repr T} {p q : RawPtr T} {n : Int} {s s' : Heap}
    (h : State.offset repr p n s q s') : s' = s := h.2

theorem write_eq {T : Type} {repr : Std.Repr T} {p : RawPtr T} {v : T} {s s' : Heap} {u : Unit}
    (h : State.write repr p v s u s') : ∃ bytes, s' = s.storeRepr p.provenance bytes := by
  obtain ⟨_, _, h⟩ := h
  obtain ⟨_, bytes, -, -, rfl⟩ := Heap.modify_run h
  exact ⟨_, rfl⟩

set_option hygiene false in
/-- Unfolds the models of the primitives in `hSpec` down to its next heap effect. -/
macro "heap_norm" : tactic => `(tactic|
  try simp only [core.ptr.from_mut, core.ptr.end_from_mut, RawPtr.allocExposure,
    RawPtr.allocSharedExposure, RawPtr.endSharedExposure, RawPtr.newBlock, RawPtr.read,
    MutRawPtr.write, RawPtr.add, RawPtr.endExposure, RawPtr.readRange, RawPtr.shareRange,
    RawPtr.endShareRange, RawPtr.borrowRange, RawPtr.endBorrowRange, RawPtr.borrowSlice,
    RawPtr.cast_const_eq, Slice.as_ptr, Slice.end_as_ptr, Slice.as_mut_ptr, Slice.end_as_mut_ptr,
    core.slice.raw.from_raw_parts, core.slice.raw.from_raw_parts_mut,
    core.slice.raw.from_raw_parts_mut.back, alloc.boxed.Box.into_raw, alloc.boxed.Box.from_raw,
    Array.as_mut_slice, Array.as_slice, Array.val_to_slice, Array.repeat_val, Array.make_val,
    Slice.from_val, Slice.length, List.replicate_succ, List.replicate_zero, UScalar.ofNatCore_val_eq,
    Array.index_mut_usize, Array.index_usize, Array.getElem?_Usize_eq,
    Result.allocatingModify, Result.checkedModify, Result.ofOption, lift, bind_ok, bind_vis,
    bind_tc_ok, bind_tc_vis, bind_tc_eq, pure_tc_eq, Std.uncurry_apply_pair] at hSpec)

/-- Proves `Heap.check s = true` for the concrete heaps of the runs, whose block bases are
variables `b` with `b.val = n`. -/
macro "heap_check" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  have := pow_numBits_gt
  simp [Heap.check, Heap.validBlock, Heap.bounded, Heap.empty, update, UScalarTy.numBits,
    Heap.validByte, Std.Repr.create, add, block,
    Heap.compatible, Heap.overlaps, List.all_eq_true, List.range_succ, List.map_cons, List.map_nil,
    List.forall_mem_cons, List.flatMap_cons, List.flatMap_nil, $hs,*]
  repeat' apply And.intro
  all_goals first
    | omega
    | (simp only [size_u32, List.length_map, List.length_cons, List.length_nil] at *; omega)
    | (intro _ _ h₁ _ _ h₂
       have := (List.mem_zipIdx h₁).2.1
       have := (List.mem_zipIdx h₂).2.1
       simp only [List.length_append, List.length_map, BitVec.toLEBytes_length, Vector.length_toList,
         List.length_nil, enc_toList_length] at *
       left; omega)))

set_option hygiene false in
/-- The next checked operation of `hSpec` has a successor `s'` (by `hx`), else the run fails. -/
macro "heap_checked" : tactic => `(tactic|
  (obtain ⟨_, s', hx, hSpec⟩ := hSpec.heap_checked (fun h => by
      simp only [Result.ofOption, Result.fail, bind_ok, bind_tc_ok, bind_tc_eq, bind_vis,
        bind_tc_vis] at h
      exact h.heap_fail)
   heap_norm))

set_option hygiene false in
/-- The run fails at its next checked operation, provided it has no successor `hx`. -/
macro "heap_stuck" : tactic => `(tactic|
  (refine hSpec.heap_stuck (fun h => by
      simp only [Result.ofOption, Result.fail, bind_ok, bind_tc_ok, bind_tc_eq, bind_vis,
        bind_tc_vis] at h
      exact h.heap_fail) ?_
   rintro ⟨_, _, hx⟩))

end safe_unsafe.Heap

namespace safe_unsafe.Heap

/-! Shared and borrowed cells. -/

theorem mapM_share_shared (l : List Std.Byte) (d : Nat) :
    (l.map (Cell.shared d)).mapM Cell.share = some (l.map (Cell.shared (d + 1))) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.mapM_cons, ih, Cell.share]

theorem mapM_borrow_shared (l : List Std.Byte) :
    (l.map (Cell.shared 0)).mapM Cell.borrow = some (l.map fun _ => Cell.borrowed) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.mapM_cons, ih, Cell.borrow]

/-- Sharing the cells of a value. -/
theorem share_at {T : Type} {repr : Std.Repr T} {r : Nat} {bytes out : Vector Cell r} {i d : Nat}
    {pre post : List Cell} {data : Vector Std.Byte repr.size}
    (hb : bytes.toList = pre ++ data.toList.map (Cell.shared d) ++ post) (hi : pre.length = i)
    (h : repr.share bytes i = some out) :
    out.toList = pre ++ data.toList.map (Cell.shared (d + 1)) ++ post := by
  unfold Std.Repr.share at h
  split at h
  · next hh =>
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h
    have hl := Std.vector_mapM_toList (f := Cell.share) (repr.select bytes i hh.2)
    rw [hm] at hl
    have hsel : (repr.select bytes i hh.2).toList = data.toList.map (Cell.shared d) := by
      rw [Std.Repr.select_toList, hb, ← hi]
      simp [List.drop_left', List.take_left']
    rw [hsel, mapM_share_shared] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    rw [Std.Repr.update_toList, hl, hb, ← hi]
    simp [List.take_left', List.drop_left']
  · simp at h

/-- Borrowing the cells of a value. -/
theorem borrow_at {T : Type} {repr : Std.Repr T} {r : Nat} {bytes out : Vector Cell r} {i : Nat}
    {pre post : List Cell} {data : Vector Std.Byte repr.size}
    (hb : bytes.toList = pre ++ data.toList.map (Cell.shared 0) ++ post) (hi : pre.length = i)
    (h : repr.borrow bytes i = some out) :
    out.toList = pre ++ data.toList.map (fun _ => Cell.borrowed) ++ post := by
  unfold Std.Repr.borrow at h
  split at h
  · next hh =>
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h
    have hl := Std.vector_mapM_toList (f := Cell.borrow) (repr.select bytes i hh.2)
    rw [hm] at hl
    have hsel : (repr.select bytes i hh.2).toList = data.toList.map (Cell.shared 0) := by
      rw [Std.Repr.select_toList, hb, ← hi]
      simp [List.drop_left', List.take_left']
    rw [hsel, mapM_borrow_shared] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    rw [Std.Repr.update_toList, hl, hb, ← hi]
    simp [List.take_left', List.drop_left']
  · simp at h

/-- Reading a value fails when its first cell is borrowed. -/
theorem read_borrowed {T : Type} {repr : Std.Repr T} {r : Nat} {bytes : Vector Cell r} {i : Nat}
    (hb : bytes.toList[i]? = some .borrowed) : repr.read bytes i = none := by
  unfold Std.Repr.read
  split
  · next hh =>
    cases hr : Std.Repr.readBytes repr.size (repr.select bytes i hh.2) with
    | none => rfl
    | some v =>
      exfalso
      obtain ⟨y, hy⟩ := Std.vector_mapM_enabled hr 0 hh.1
      have h0 := Std.Repr.select_getElem? repr bytes i hh.2 0 hh.1
      rw [Nat.add_zero, hb, Vector.getElem?_eq_getElem hh.1] at h0
      rw [Option.some.inj h0] at hy
      simp [Cell.read] at hy
  · rfl

/-- Writing a value fails when its first cell is not writable. -/
theorem write_unwritable {T : Type} {repr : Std.Repr T} {r : Nat} {bytes : Vector Cell r}
    {i : Nat} {c : Cell} (hb : bytes.toList[i]? = some c) (hc : ∀ x, c.write x = none) (v : T)
    (data : Vector Std.Byte repr.size) (he : repr.encode v data) :
    repr.write bytes i v data he = none := by
  unfold Std.Repr.write
  split
  · next hh =>
    cases hr : Std.Repr.writeBytes repr.size (repr.select bytes i hh.2) data with
    | none => rfl
    | some v =>
      exfalso
      obtain ⟨y, hy⟩ := Std.vector_mapM_enabled hr 0 hh.1
      have h0 := Std.Repr.select_getElem? repr bytes i hh.2 0 hh.1
      rw [Nat.add_zero, hb, Vector.getElem?_eq_getElem hh.1] at h0
      simp only [Vector.getElem_zip] at hy
      rw [Option.some.inj h0, hc] at hy
      simp at hy
  · rfl

end safe_unsafe.Heap

namespace safe_unsafe.Heap

theorem mapM_read_shared (l : List Std.Byte) (d : Nat) :
    (l.map (Cell.shared d)).mapM Cell.read = some l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.mapM_cons, ih, Cell.read]

/-- Reading the cells of an encoding. -/
theorem read_at {T : Type} {repr : Std.Repr T} {r : Nat} {bytes : Vector Cell r} {i d : Nat}
    {pre post : List Cell} {data : Vector Std.Byte repr.size} {v : T}
    (hb : bytes.toList = pre ++ data.toList.map (Cell.shared d) ++ post) (hi : pre.length = i)
    (he : repr.encode v data) (hpos : 0 < repr.size) : repr.read bytes i = some v := by
  have hr : i + repr.size ≤ r := by
    have := congrArg List.length hb
    simp at this; omega
  unfold Std.Repr.read
  simp only [hpos, hr, and_self, ↓reduceDIte]
  have hl := Std.vector_mapM_toList (f := Cell.read) (repr.select bytes i hr)
  have hsel : (repr.select bytes i hr).toList = data.toList.map (Cell.shared d) := by
    rw [Std.Repr.select_toList, hb, ← hi]
    simp [List.drop_left', List.take_left']
  rw [hsel, mapM_read_shared] at hl
  have : Std.Repr.readBytes repr.size (repr.select bytes i hr) = some data := by
    unfold Std.Repr.readBytes
    cases h : (repr.select bytes i hr).mapM Cell.read with
    | none => rw [h] at hl; simp at hl
    | some w => rw [h] at hl; simp at hl; rw [Vector.toList_inj.mp hl]
  rw [this]
  exact repr.encode_decode _ _ he

end safe_unsafe.Heap
