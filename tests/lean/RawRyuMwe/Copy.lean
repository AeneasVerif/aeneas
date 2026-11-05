module

public import RawRyuMwe.Windows
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Heap.Repr

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic scalar_mwe
open scoped Aeneas.Std.HeapWP

namespace scalar_mwe

theorem copy_chunk.spec (source destination : RawPtr U8) (sourceBase destinationBase : BasePtr)
    (values : Vector U8 n) (old : Vector Aeneas.Std.Byte n) (depth : Nat)
    (positive : 0 < n)
    (apart : source.address.val + n ≤ destination.address.val ∨
      destination.address.val + n ≤ source.address.val) :
    HeapWP.Triple (bytesAt destination destinationBase old.toList ∗
      bytesAt source sourceBase (values.toList.map Byte.data) depth)
      (RawPtr.copy_nonoverlapping_bytes source destination n)
      (fun _ => bytesAt destination destinationBase (values.toList.map Byte.data) ∗
        bytesAt source sourceBase (values.toList.map Byte.data) depth) := by
  have run := HeapWP.copy_bytes.spec (raw_memory_views.byteVectorRepr n) source destination
    sourceBase destinationBase values old depth positive
    (raw_memory_views.byteVectorRepr_noPointers values)
    (fun a b ha hb => ha.trans hb.symm) apart
  intro h F s₀ hp hd hm hi
  have pre :
      (block (raw_memory_views.byteVectorRepr n) (destination.cast (Vector U8 n))
        destinationBase (old.map (Cell.shared 0)).toList ∗
      pointsTo (raw_memory_views.byteVectorRepr n) (source.cast (Vector U8 n))
        sourceBase values depth) h := by
    simpa [sep, pointsTo, raw_memory_views.byteVectorRepr, bytesAt, block,
      RawPtr.cast, RawPtr.offsetFrom, Repr.u8, Vector.toList_map] using hp
  apply HeapWP.Spec.mono (run h F s₀ pre hd hm hi)
  rintro result s₁ ⟨h₁, hd₁, hm₁, hi₁, hp₁⟩
  refine ⟨h₁, hd₁, hm₁, hi₁, ?_⟩
  simpa [sep, pointsTo, raw_memory_views.byteVectorRepr, bytesAt, block,
    RawPtr.cast, RawPtr.offsetFrom, Repr.u8, Vector.toList_map] using hp₁

theorem copy_windows.spec (source sourceAt destination destinationAt : RawPtr U8)
    (sourceBase destinationBase : BasePtr) (sourceValues : List U8)
    (old : List Aeneas.Std.Byte) (sourceOffset destinationOffset width depth : Nat)
    (sourceBound : sourceOffset + width ≤ sourceValues.length)
    (destinationBound : destinationOffset + width ≤ old.length) (positive : 0 < width)
    (sourceProv : sourceAt.provenance = source.provenance)
    (sourceAddr : sourceAt.address.val = source.address.val + sourceOffset)
    (destProv : destinationAt.provenance = destination.provenance)
    (destAddr : destinationAt.address.val = destination.address.val + destinationOffset)
    (apart : sourceAt.address.val + width ≤ destinationAt.address.val ∨
      destinationAt.address.val + width ≤ sourceAt.address.val) :
    HeapWP.Triple (bytesAt source sourceBase (sourceValues.map Byte.data) depth ∗
      bytesAt destination destinationBase old)
      (RawPtr.copy_nonoverlapping_bytes sourceAt destinationAt width)
      (fun _ => bytesAt source sourceBase (sourceValues.map Byte.data) depth ∗
        bytesAt destination destinationBase
          (old.take destinationOffset ++
            ((sourceValues.drop sourceOffset).take width).map Byte.data ++
            old.drop (destinationOffset + width))) := by
  let selected : Vector U8 width :=
    ⟨((sourceValues.drop sourceOffset).take width).toArray, by simp; agrind⟩
  let previous : Vector Aeneas.Std.Byte width :=
    ⟨((old.drop destinationOffset).take width).toArray, by simp; agrind⟩
  have chunk := copy_chunk.spec sourceAt destinationAt sourceBase destinationBase
    selected previous depth positive apart
  have inner := window_frame.spec destination destinationAt destinationBase
    (old.map (Cell.shared 0)) ((selected.toList.map Byte.data).map (Cell.shared 0))
    destinationOffset width
    (bytesAt sourceAt sourceBase (selected.toList.map Byte.data) depth)
    (bytesAt sourceAt sourceBase (selected.toList.map Byte.data) depth)
    (fun _ : Unit => True) (by simpa using destinationBound) (by simp) destProv destAddr
    (RawPtr.copy_nonoverlapping_bytes sourceAt destinationAt width)
    (HeapWP.Triple.conseq (fun _ hp => hp) (fun _ _ hp => ⟨True.intro, hp⟩)
      (by simpa [previous, bytesAt, List.map_drop, List.map_take] using chunk))
  have reordered : HeapWP.Triple
      (bytesAt sourceAt sourceBase (selected.toList.map Byte.data) depth ∗
        bytesAt destination destinationBase old)
      (RawPtr.copy_nonoverlapping_bytes sourceAt destinationAt width)
      (fun _ h => True ∧ (bytesAt sourceAt sourceBase (selected.toList.map Byte.data) depth ∗
        bytesAt destination destinationBase (old.take destinationOffset ++
          selected.toList.map Byte.data ++ old.drop (destinationOffset + width))) h) := by
    intro h F s hp hd hm hi
    apply HeapWP.Spec.mono (inner h F s ((sep_comm _ _ h).mp hp) hd hm hi)
    rintro result s₁ ⟨h₁, hd₁, hm₁, hi₁, ht, cells⟩
    refine ⟨h₁, hd₁, hm₁, hi₁, ht, ?_⟩
    apply (sep_comm _ _ h₁).mp
    simpa [bytesAt, List.map_append, List.map_take, List.map_drop] using cells
  have outer := window_frame.spec source sourceAt sourceBase
    ((sourceValues.map Byte.data).map (Cell.shared depth))
    ((selected.toList.map Byte.data).map (Cell.shared depth))
    sourceOffset width (bytesAt destination destinationBase old)
    (bytesAt destination destinationBase (old.take destinationOffset ++
      selected.toList.map Byte.data ++ old.drop (destinationOffset + width)))
    (fun _ : Unit => True) (by simpa using sourceBound) (by simp) sourceProv sourceAddr
    (RawPtr.copy_nonoverlapping_bytes sourceAt destinationAt width)
    (by simpa [selected, bytesAt, List.map_drop, List.map_take, List.map_append] using reordered)
  have rejoin (xs : List Cell) : xs.take sourceOffset ++
      (xs.drop sourceOffset).take width ++ xs.drop (sourceOffset + width) = xs := by
    rw [← List.drop_drop, List.append_assoc, List.take_append_drop, List.take_append_drop]
  have result := HeapWP.Triple.conseq (fun _ hp => hp) (fun _ _ hp => hp.2) outer
  simpa only [selected, Vector.toList_mk, List.toList_toArray, bytesAt,
    List.map_take, List.map_drop, ← List.map_append, rejoin] using result

def copiedBytes (source : List U8) (old : List Aeneas.Std.Byte)
    (sourceOffset destinationOffset width : Nat) : List Aeneas.Std.Byte :=
  old.take destinationOffset ++ ((source.drop sourceOffset).take width).map Byte.data ++
    old.drop (destinationOffset + width)

theorem copiedBytes_length (source : List U8) (old : List Aeneas.Std.Byte)
    (sourceOffset destinationOffset width : Nat)
    (hs : sourceOffset + width ≤ source.length) (hd : destinationOffset + width ≤ old.length) :
    (copiedBytes source old sourceOffset destinationOffset width).length = old.length := by
  simp only [copiedBytes, List.length_append, List.length_take, List.length_drop, List.length_map]
  agrind

def copy_scoped (source : List U8) (old : List Aeneas.Std.Byte)
    (sourceAddress destinationAddress : BasePtr) (sourceOffset destinationOffset : Usize)
    (width : Nat) : Result (List Aeneas.Std.Byte) := do
  let src ← exposeBytes (source.map Byte.data) 1 sourceAddress
  let dst ← exposeBytes old 0 destinationAddress
  let srcAt ← RawPtr.add Repr.u8 src sourceOffset
  let dstAt ← RawPtr.add Repr.u8 dst destinationOffset
  RawPtr.copy_nonoverlapping_bytes srcAt dstAt width
  let updated ← snapshotBytes dst
  closeBytes dst old.length 0
  closeBytes src source.length 1
  pure updated

theorem copy_scoped.spec (source : List U8) (old : List Aeneas.Std.Byte)
    (sourceAddress destinationAddress : BasePtr) (sourceOffset destinationOffset : Usize)
    (width : Nat) (positive : 0 < width)
    (hs : sourceOffset.val + width ≤ source.length)
    (hd : destinationOffset.val + width ≤ old.length)
    (apart : sourceAddress.val + sourceOffset.val + width ≤ destinationAddress.val + destinationOffset.val ∨
      destinationAddress.val + destinationOffset.val + width ≤ sourceAddress.val + sourceOffset.val)
    (F : Fragment) (s₀ : Heap) (hm : Fragment.Matches s₀ F) (hi : s₀.Inv) :
    HeapWP.Spec (copy_scoped source old sourceAddress destinationAddress sourceOffset destinationOffset width)
      (fun result s₁ => result = copiedBytes source old sourceOffset.val destinationOffset.val width ∧
        s₁.Inv ∧ Fragment.Matches s₁ F) s₀ := by
  let new := copiedBytes source old sourceOffset.val destinationOffset.val width
  have length : new.length = old.length := copiedBytes_length source old _ _ _ hs hd
  unfold copy_scoped
  apply HeapWP.Spec.bind (exposeBytes.spec _ 1 sourceAddress s₀ F hi hm)
  rintro src s₁ ⟨srcAddr, _, h₁, hd₁, hm₁, hi₁, hp₁⟩
  apply HeapWP.Spec.bind (exposeBytes.spec old 0 destinationAddress s₁ (h₁ ∪ F) hi₁ hm₁)
  rintro dst s₂ ⟨dstAddr, _, h₂, hd₂, hm₂, hi₂, hp₂⟩
  have matching : Fragment.Matches s₂ (h₁ ∪ (h₂ ∪ F)) := by
    simpa [Fragment.matches_union, and_left_comm] using hm₂
  apply HeapWP.Spec.bind (add_storage.spec src (source.map Byte.data) 1 sourceOffset
    (by simp; agrind) h₁ (h₂ ∪ F) s₂ hp₁ matching hi₂)
  rintro srcAt s₃ ⟨srcProv, srcOffset, stateEq⟩
  subst s₃
  apply HeapWP.Spec.bind (add_storage.spec dst old 0 destinationOffset (by agrind)
    h₂ (h₁ ∪ F) s₂ hp₂ hm₂ hi₂)
  rintro dstAt s₃ ⟨dstProv, dstOffset, stateEq⟩
  subst s₃
  have separated : h₁.Disjoint h₂ := (Fragment.disjoint_union_right.mp hd₂).1.symm
  have frames : (h₁ ∪ h₂).Disjoint F :=
    Fragment.disjoint_union_left.mpr ⟨hd₁, (Fragment.disjoint_union_right.mp hd₂).2⟩
  have copy := copy_windows.spec src srcAt dst dstAt src.address dst.address source old
    sourceOffset.val destinationOffset.val width 1 hs hd positive srcProv srcOffset dstProv dstOffset
    (by simpa [srcOffset, dstOffset, srcAddr, dstAddr] using apart)
  have copy' : HeapWP.Triple
      (bytesAt src src.address (source.map Byte.data) 1 ∗ bytesAt dst dst.address old)
      (RawPtr.copy_nonoverlapping_bytes srcAt dstAt width)
      (fun _ h => True ∧
        (bytesAt src src.address (source.map Byte.data) 1 ∗ bytesAt dst dst.address new) h) :=
    HeapWP.Triple.conseq (fun _ hp => hp) (fun _ _ hp => ⟨True.intro, hp⟩) copy
  have body := preserve_two_storage src dst _ _ old new 1 0 _ (fun _ => True) rfl length copy'
  apply HeapWP.Spec.bind (body (h₁ ∪ h₂) F s₂
    ⟨h₁, h₂, separated, rfl, hp₁, hp₂⟩ frames
    (by simpa [Fragment.union_assoc] using matching) hi₂)
  rintro _ s₃ ⟨h₃, hd₃, hm₃, hi₃, _, sourceH, destH, disj, union, sourceP, destP⟩
  have destFrame : destH.Disjoint (sourceH ∪ F) :=
    Fragment.disjoint_union_right.mpr ⟨disj.symm, (Fragment.disjoint_union_left.mp (union ▸ hd₃)).2⟩
  have destMatch : Fragment.Matches s₃ (destH ∪ (sourceH ∪ F)) := by
    simp only [union, Fragment.matches_union] at hm₃ ⊢
    tauto
  apply HeapWP.Spec.bind (snapshotBytes.spec dst new 0 destH (sourceH ∪ F) s₃ destP destMatch)
  rintro updated s₄ ⟨updatedEq, stateEq⟩
  subst updated
  subst s₄
  have closeDest := closeBytes.state_spec dst new 0 destH (sourceH ∪ F)
    s₃ destP destFrame destMatch hi₃
  rw [length] at closeDest
  apply HeapWP.Spec.bind closeDest
  rintro _ s₄ ⟨hi₄, hm₄, _, _⟩
  have closeSource := closeBytes.state_spec src (source.map Byte.data) 1 sourceH F s₄
    sourceP (Fragment.disjoint_union_left.mp (union ▸ hd₃)).1 hm₄ hi₄
  simp only [List.length_map] at closeSource
  apply HeapWP.Spec.bind closeSource
  rintro _ s₅ ⟨hi₅, hm₅, _, _⟩
  exact (HeapWP.Spec.pure _ _ _).mpr ⟨rfl, hi₅, hm₅⟩

end scalar_mwe
