module
public meta import Aeneas.Extract.Extract
public import Aeneas.Std.Core.Fmt
public section

namespace Aeneas.Std

-- TODO
@[rust_type "core::panic::panic_info::PanicInfo"]
axiom core.panic.panic_info.PanicInfo : Type

/-! The functions that rustc calls to panic. Charon references them from panics, failed assertions
    and aborted unwinds; they all simply fail. -/

@[expose, rust_fun "core::panicking::panic"]
def core.panicking.panic (_ : Str) : Result Never := .fail .panic

@[expose, rust_fun "core::panicking::panic_fmt"]
def core.panicking.panic_fmt (_ : core.fmt.Arguments) : Result Never := .fail .panic

@[expose, rust_fun "core::panicking::panic_in_cleanup"]
def core.panicking.panic_in_cleanup : Result Never := .fail .panic

@[expose, rust_fun "core::panicking::panic_no_unwind"]
def core.panicking.panic_no_unwind : Result Never := .fail .panic

@[expose, rust_fun "core::panicking::assert_failed"]
def core.panicking.assert_failed {T U : Type _} (_ : core.fmt.Debug T) (_ : core.fmt.Debug U)
  (_ : core.panicking.AssertKind) (_ : T) (_ : U) (_ : Option core.fmt.Arguments) :
  Result Never := .fail .panic

end Aeneas.Std
