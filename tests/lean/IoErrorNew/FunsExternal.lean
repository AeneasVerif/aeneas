module
public import Aeneas
public import IoErrorNew.Types
@[expose] public section

namespace Aeneas.Std
open io_error_new

def strError : core.error.Error Str := {
  fmtDebugInst := { fmt := fun _ fmt => Result.ok (core.result.Result.Ok (), fmt) }
  fmtDisplayInst := { fmt := fun _ fmt => Result.ok (core.result.Result.Ok (), fmt) }
}

/-- Keep the string in the trait object produced by the standard conversion. -/
@[rust_fun "alloc::boxed::convert::{core::convert::From<Box<@>, &'0 str>}::from"]
def Box.Insts.CoreConvertFromShared0Str.from
    (text : Str) : Result (Dyn (fun T => core.error.Error T)) :=
  Result.ok ⟨Str, strError, text⟩

/-- The payload is abstracted, but conversion is still evaluated and can fail. -/
@[rust_fun "alloc::io::error::{core::io::error::Error}::new"]
def alloc.io.error.Error.new {E : Type _}
    (intoInst : core.convert.Into E (Dyn (fun T => core.error.Error T)))
    (_kind : core.io.error.ErrorKind) (error : E) : Result core.io.error.Error := do
  let _ ← intoInst.into error
  Result.ok ()

end Aeneas.Std
