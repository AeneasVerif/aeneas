import Transmutes

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Result

/-! Invalid reinterpretations of memory fail in the model. -/

namespace transmutes

/-- Any byte other than `0` and `1` is not a `bool`: the transmute fails. -/
theorem bool_of_byte.fails (b : U8) (h : 1 < b.val) : ifails emp (bool_of_byte b) := by
  unfold bool_of_byte core.mem.transmute
  refine ifails_bind (R := fun cs => ⌜cs = Pointee.toCells (T := U8) b⌝) ?_ fun cs => ?_
  · apply ispec_guardedModify
    intro h _ frame hCompatible
    exact ⟨⟨rfl, rfl⟩, h, hCompatible, rfl, rfl⟩
  · refine ifails_mono (entails_of_eq (sep_emp_r_eq _).symm) (ifails_ipure fun hcs => ?_)
    subst hcs
    apply Pointee.decode.fails
    rw [Pointee.toCells_u8]
    show (([some b] : List (Option U8)).mapM id >>= fun bytes =>
      match bytes with
      | [byte] => if byte.val = 0 then some false else if byte.val = 1 then some true else none
      | _ => none) = none
    simp [show b.val ≠ 0 by omega, show b.val ≠ 1 by omega]

/-- An aligned `u16` read at an odd offset of a byte buffer fails: the model only knows that the
buffer is aligned to `1` (in Rust, this is undefined behavior if the address is odd). -/
theorem read_u16_misaligned.fails (buf : Std.Array U8 4#usize) :
    ifails emp (read_u16_misaligned buf) := by
  unfold read_u16_misaligned
  simp only [lift, Std.bind_ok]
  refine ifails_bind (Slice.as_ptr.spec _) fun ⟨p, back⟩ => ?_
  simp only [Std.uncurry]
  refine ifails_ipure fun _ => ifails_ipure fun _ => ?_
  -- The view starts its allocation: `freeable` gives the offset `0`
  refine ifails_mono (fun h ⟨_, h₂, _, _, _, hF⟩ =>
    (sep_pure_l _ _ h).mpr ⟨((RawPtr.freeable_holds p h₂).mp hF).1, ‹_›⟩)
    (ifails_ipure fun hOffset => ?_)
  refine ifails_bind (ispec_frame (RawPtr.add.spec p _ 1#usize (by simp)) (p.freeable _ .view))
    fun q => ?_
  refine ifails_mono (P' := iprop(⌜q = p.shift 1⌝ ∗ emp)) (by iframe) (ifails_ipure fun hq => ?_)
  subst hq
  refine ifails_bind_left (RawPtr.read.fails_misaligned _ ?_)
  simp [RawPtr.Aligned, RawPtr.shift, hOffset]

/-! Regression tests of the reviews of the byte layouts: pointer arithmetic over the cells of
another type, `write_bytes` on typed cells, and accesses through null pointers which touch no
cell, all fail. -/

/-- A `char` cell is not a byte (`char` has more values). -/
theorem typedCell_char_ne_u8 : TypedCell Char ≠ U8 := by
  intro h
  have hInj : Function.Injective fun f : Fin Char.numCodePoints =>
      (cast h (⟨Char.ofOrdinal f⟩ : TypedCell Char) : U8).bv.toFin := by
    intro f g hfg
    have hbv := BitVec.toFin_inj.mp hfg
    have hcast : cast h (⟨Char.ofOrdinal f⟩ : TypedCell Char) = cast h ⟨Char.ofOrdinal g⟩ :=
      (U8.eq_equiv_bv_eq _ _).mpr hbv
    exact Char.ofOrdinal_injective (TypedCell.mk.inj (cast_inj h |>.mp hcast))
  have := Fintype.card_le_of_injective _ hInj
  simp [Char.numCodePoints] at this

/-- The cells of a range, located through a pointer `l` at the same place as `q`. -/
theorem pointsToRange_eq_array {T : Type} [Pointee T] {M : Mutability} (q : RawPtr T M)
    (vs : List T) (l : Loc) (hl : l = q.loc) :
    (q ↦* vs) = owns (Heap.array l (vs.flatMap Pointee.toCells)) := by
  rw [hl]; rfl

/-- Rust returns `buf[4]` (a `*const char` moves by 4 bytes): the model fails, since `add` on a
`char` pointer requires `char` cells. -/
theorem char_add_over_bytes.fails (buf : Std.Array U8 8#usize) :
    ifails emp (char_add_over_bytes buf) := by
  unfold char_add_over_bytes
  simp only [lift, Std.bind_ok]
  refine ifails_bind (Slice.as_ptr.spec _) fun ⟨p, back⟩ => ?_
  simp only [Std.uncurry]
  refine ifails_ipure fun _ => ifails_ipure fun _ => ifails_bind_left ?_
  rw [pointsToRange_eq_array p _ (RawPtr.cast Char p).loc rfl]
  exact ifails_mono (by iframe) (RawPtr.add.fails_cells (RawPtr.cast Char p) _ 1#usize
    (fun h => typedCell_char_ne_u8 h.symm) (by rw [Pointee.length_flatMap_toCells]; simp) (by simp))

/-- Rust returns `a[1]`: the model fails (byte arithmetic over `char` cells). -/
theorem char_array_bytes.fails (a : Std.Array Char 8#usize) :
    ifails emp (char_array_bytes a) := by
  unfold char_array_bytes
  simp only [lift, Std.bind_ok]
  refine ifails_bind (Slice.as_ptr.spec _) fun ⟨p, back⟩ => ?_
  simp only [Std.uncurry]
  refine ifails_ipure fun _ => ifails_ipure fun _ => ifails_bind_left ?_
  rw [pointsToRange_eq_array p _ (RawPtr.cast U8 p).loc rfl]
  exact ifails_mono (by iframe) (RawPtr.add.fails_cells (RawPtr.cast U8 p) _ 4#usize
    typedCell_char_ne_u8 (by rw [Pointee.length_flatMap_toCells]; simp) (by simp))

/-- Rust returns `1`: the model fails (`offset_from` on `char` pointers over bytes). -/
theorem char_offset_from.fails (buf : Std.Array U8 8#usize) :
    ifails emp (char_offset_from buf) := by
  unfold char_offset_from
  simp only [lift, Std.bind_ok]
  refine ifails_bind (Slice.as_ptr.spec _) fun ⟨p, back⟩ => ?_
  simp only [Std.uncurry]
  refine ifails_ipure fun _ => ifails_ipure fun _ => ?_
  refine ifails_bind (ispec_frame (RawPtr.add.spec p _ 4#usize (by simp)) (p.freeable _ .view))
    fun q => ?_
  refine ifails_mono (P' := iprop(⌜q = p.shift 4⌝ ∗ p ↦* buf.to_slice.val)) (by iframe)
    (ifails_ipure fun hq => ?_)
  subst hq
  refine ifails_bind_left ?_
  rw [pointsToRange_eq_array p _ ⟨(RawPtr.cast Char (p.shift 4)).loc.allocId,
    min (RawPtr.cast Char (p.shift 4)).loc.offset (RawPtr.cast Char p).loc.offset⟩
    (by ext <;> simp [RawPtr.shift])]
  exact RawPtr.offset_from.fails_cells _ _ _ (fun h => typedCell_char_ne_u8 h.symm)
    (by rw [Pointee.length_flatMap_toCells]; simp) (by simp [RawPtr.shift])

/-- Rust writes 4 bytes: the model fails, since `write_bytes` requires byte cells. -/
theorem write_bytes_char.fails (buf : Std.Array U32 2#usize) :
    ifails emp (write_bytes_char buf) := by
  unfold write_bytes_char
  simp only [lift, Std.bind_ok]
  refine ifails_bind (Slice.as_mut_ptr.spec _) fun ⟨p, back⟩ => ?_
  simp only [Std.uncurry]
  exact ifails_bind_left (core.ptr.write_bytes.fails _ _ _
    fun h => typedCell_char_ne_u8 h.1)

/-- Reading a zero-sized value through the null pointer fails. -/
theorem read_null_zst.fails : ifails emp read_null_zst :=
  RawPtr.read.fails_misaligned _ (RawPtr.not_aligned_null (by simp))

/-- `write_bytes` through the null pointer fails, even when no byte is written. -/
theorem write_bytes_null.fails : ifails emp write_bytes_null := by
  unfold write_bytes_null write_bytes_zero
  exact core.ptr.write_bytes.fails _ _ _ fun h => h.2.2 (by simp) rfl

/-- `slice::from_raw_parts` on the null pointer fails, even for an empty slice. -/
theorem empty_slice_of_null.fails : ifails emp empty_slice_of_null := by
  unfold empty_slice_of_null slice_of_raw_parts core.slice.raw.from_raw_parts
  exact ifails_bind_left (ifails_bind_left (Result.require.fails fun h => h.2 (by simp) rfl))

/-- A unit cell is not a byte. -/
theorem typedCell_unit_ne_u8 : TypedCell Unit ≠ U8 := by
  intro h
  have hs : ∀ a b : TypedCell Unit, a = b := fun ⟨()⟩ ⟨()⟩ => rfl
  have := congrArg (cast h) (hs (cast h.symm 0#u8) (cast h.symm 1#u8))
  simp at this

/-- Rust returns `true` (`add` on `*const ()` does not move): the model fails, since the cells
between the two byte pointers are not bytes. -/
theorem zst_eq.fails (a : Std.Array Unit 4#usize) : ifails emp (zst_eq a) := by
  unfold zst_eq
  simp only [lift, Std.bind_ok]
  refine ifails_bind (Slice.as_ptr.spec _) fun ⟨p, back⟩ => ?_
  simp only [Std.uncurry]
  refine ifails_ipure fun _ => ifails_ipure fun _ => ?_
  refine ifails_bind (ispec_frame (RawPtr.add.spec p a.to_slice.val 1#usize (by simp))
    (p.freeable _ .view)) fun q => ?_
  refine ifails_mono (P' := iprop(⌜q = p.shift 1⌝ ∗ p ↦* a.to_slice.val)) (by iframe)
    (ifails_ipure fun hq => ?_)
  subst hq
  refine ifails_bind_left ?_
  rw [pointsToRange_eq_array p _ p.loc rfl]
  have hLen : 0 < (a.to_slice.val.flatMap Pointee.toCells).length := by
    rw [Pointee.length_flatMap_toCells]; simp
  have hNe : (RawPtr.cast U8 p).loc ≠ (RawPtr.cast U8 (p.shift 1)).loc := by
    simp only [RawPtr.shift]; intro h; simpa using congrArg Loc.offset h
  rw [RawPtr.eq, ite_eq_right hNe]
  apply ifails_guardedModify
  intro h hCells h' hSub hPre
  have hc := HeapOp.isValid_of_array (i := 0) (IProp.up_closed _ hCells hSub) hLen
  rcases hPre.2 with ⟨_, hLive⟩ | ⟨⟨_, hBox, _⟩, _⟩
  · exact typedCell_unit_ne_u8 (Heap.isValid_unique hc (hLive 0 (by simp [RawPtr.shift]))
      (by simp [RawPtr.shift]))
  · exact typedCell_unit_ne_u8 (Heap.isValid_unique hc hBox (by simp))

end transmutes
