module
public import Aeneas.Std.RawPtrOps
public import Aeneas.Std.Core.Cmp
public import Aeneas.Std.Core.Fmt
@[expose] public section

namespace Aeneas.Std

open Result

@[rust_type "core::ptr::non_null::NonNull"]
abbrev core.ptr.non_null.NonNull (T : Type) := MutRawPtr T

/-- The allocator never hands out the allocation identifier `0` (see
`Heap.freshBase`). -/
@[rust_fun "core::ptr::non_null::{core::ptr::non_null::NonNull<@T>}::dangling"]
def core.ptr.non_null.NonNull.dangling (T : Type) : Result (core.ptr.non_null.NonNull T) :=
  ok ⟨⟨0, 0⟩, 0⟩

@[rust_fun "core::ptr::non_null::{core::ptr::non_null::NonNull<@T>}::as_ptr"]
def core.ptr.non_null.NonNull.as_ptr {T : Type} (p : core.ptr.non_null.NonNull T) :
    Result (MutRawPtr T) :=
  ok p

@[rust_fun "core::ptr::non_null::{core::ptr::non_null::NonNull<@T>}::as_ref"]
def core.ptr.non_null.NonNull.as_ref {T : Type} [ByteRepr T] (p : core.ptr.non_null.NonNull T) :
    Result T :=
  p.read

@[rust_fun "core::ptr::non_null::{core::ptr::non_null::NonNull<@T>}::as_mut"]
def core.ptr.non_null.NonNull.as_mut {T : Type} [ByteRepr T] (p : core.ptr.non_null.NonNull T) :
    Result (T × (T → Result Unit) × core.ptr.non_null.NonNull T) :=
  bind (MutRawPtr.take p) fun v => ok (v, fun v' => MutRawPtr.restore p v', p)

@[rust_fun
  "core::ptr::non_null::{core::fmt::Debug<core::ptr::non_null::NonNull<@T>>}::fmt"]
def core.ptr.non_null.NonNull.Insts.CoreFmtDebug.fmt {T : Type} (_ : core.ptr.non_null.NonNull T)
    (fmt : core.fmt.Formatter) :
    Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  ok (.Ok (), fmt)

@[reducible, rust_trait_impl "core::fmt::Debug<core::ptr::non_null::NonNull<@T>>"]
def core.ptr.non_null.NonNull.Insts.CoreFmtDebug (T : Type) :
    core.fmt.Debug (core.ptr.non_null.NonNull T) := {
  fmt := core.ptr.non_null.NonNull.Insts.CoreFmtDebug.fmt
}

@[rust_fun
  "core::ptr::non_null::{core::cmp::PartialEq<core::ptr::non_null::NonNull<@T>, core::ptr::non_null::NonNull<@T>>}::eq"]
def core.ptr.non_null.NonNull.Insts.CoreCmpPartialEqNonNull.eq {T : Type}
    (p q : core.ptr.non_null.NonNull T) : Result Bool :=
  ok (decide (p.base = q.base ∧ p.offset = q.offset))

@[reducible, rust_trait_impl
  "core::cmp::PartialEq<core::ptr::non_null::NonNull<@T>, core::ptr::non_null::NonNull<@T>>"]
def core.ptr.non_null.NonNull.Insts.CoreCmpPartialEqNonNull (T : Type) :
    core.cmp.PartialEq (core.ptr.non_null.NonNull T) (core.ptr.non_null.NonNull T) := {
  eq := core.ptr.non_null.NonNull.Insts.CoreCmpPartialEqNonNull.eq
}

attribute [step_simps] core.ptr.non_null.NonNull.dangling core.ptr.non_null.NonNull.as_ptr
  core.ptr.non_null.NonNull.as_ref core.ptr.non_null.NonNull.Insts.CoreCmpPartialEqNonNull.eq

end Aeneas.Std
