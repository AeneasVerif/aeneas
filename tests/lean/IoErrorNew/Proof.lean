import IoErrorNew.Funs

open Aeneas.Std io_error_new

theorem direct_error_constructs (text : Str) :
    make_invalid_data text = Result.ok () := by
  simp [make_invalid_data, Aeneas.Std.alloc.io.error.Error.new,
    Aeneas.Std.core.convert.IntoFrom.into,
    Aeneas.Std.Box.Insts.CoreConvertFromShared0Str.from]
  rfl

private def failingConversion :
    Aeneas.Std.core.convert.Into Unit
      (Aeneas.Std.Dyn (fun T => Aeneas.Std.core.error.Error T)) := {
  into := fun _ => Result.fail .panic
}

theorem conversion_failure_propagates :
    Aeneas.Std.alloc.io.error.Error.new failingConversion
      core.io.error.ErrorKind.InvalidData () = Result.fail .panic := by
  simp [Aeneas.Std.alloc.io.error.Error.new, failingConversion]
