module

public import RawZmijMwe.Formatter
import all RawZmijMwe.Decimal
import all Aeneas.Std.Heap.Model

@[expose] public section

open Aeneas Aeneas.Std scalar_mwe

namespace raw_zmij_mwe.regression

def address : BasePtr := ⟨BitVec.ofNat _ 256⟩

def exposeAt (bytes : List Aeneas.Std.Byte) (depth root : Nat) (s : Heap) :
    Option (RawPtr U8 × Heap) := do
  let (id, s) ← s.createRepr ⟨address, root, bytes.map (Cell.shared depth), false, true, true⟩
  pure (⟨id, address⟩, s)

/- Concrete successful heap-protocol trace, not an interpreter for Result.
   The decimal writer itself is covered by write_decimal.spec. This exercises
   the adapter's placement/root choices rather than relying on accepted OOM. -/
def formatTrace (old : List Aeneas.Std.Byte) (value : U8) (s₀ : Heap) :
    Option (List Aeneas.Std.Byte × Heap) := do
  let (start, s₁) ← exposeAt old 0 0 s₀
  let (finish, s₂) ← (decimalDigits value).foldlM
    (fun (cursor, s) digit => do
      let s ← Heap.write Repr.u8 cursor digit #v[.data digit] rfl s
      let next ← Heap.offset Repr.u8 cursor 1 s
      pure (next, s)) (start, s₁)
  let blk ← s₂.allocations start.provenance
  let updated ← blk.repr.mapM Cell.read
  let s₃ ← Heap.endExposureAt Repr.u8 start 4 0 s₂
  if (Heap.read Repr.u8 start s₃).isSome then none else do
    let (origin, s₄) ← exposeAt updated 1 0 s₃
    let len ← Heap.distance Repr.u8 finish origin s₄
    if len != (decimalDigits value).length then none else do
      let s₅ ← Heap.endExposureAt Repr.u8 origin 4 1 s₄
      let (ptr, s₆) ← exposeAt updated 1 0 s₅
      let bytes ← Heap.readRange Repr.u8 ptr len.toNat s₆
      if bytes != decimalDigits value then none else do
        let s₇ ← Heap.shareRange Repr.u8 ptr len.toNat s₆
        let s₈ ← Heap.endShareRange Repr.u8 ptr len.toNat s₇
        let s₉ ← Heap.endExposureAt Repr.u8 ptr 4 1 s₈
        if start.provenance == origin.provenance || origin.provenance == ptr.provenance then none
        else pure (updated, s₉)

def reusedBuffer : Option Bool := do
  let (bytes, s) ← ([0#u8, 9#u8, 10#u8, 99#u8, 100#u8, 255#u8, 7#u8]).foldlM
    (fun (old, s) value => formatTrace old value s)
    (List.replicate 4 .uninit, Heap.empty)
  pure (s.check && s.next == 21 &&
    bytes == [.data 55#u8, .data 53#u8, .data 53#u8, .uninit])

example : reusedBuffer = some true := by native_decide

end raw_zmij_mwe.regression
