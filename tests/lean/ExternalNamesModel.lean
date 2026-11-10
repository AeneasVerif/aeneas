module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result

/-- A hand-written model for `external_names::is_mult`.

    `tests/external-names/external-names.json` maps the Rust function to this
    definition, and the test passes `-extra-includes=ExternalNamesModel` so that
    the generated file imports it. Nothing here belongs to the Core/Std/Alloc
    models which ship with the compiler: that is the point of the test - a list
    of external names may point at definitions of the user's own library. -/
def ExternalNamesModel.isMult (n m : U32) : Result Bool :=
  ok (n.val % m.val == 0)

/-- A hand-written model for the opaque `external_names_split::Counter`,
    which `tests/external-names/external-names-split.json` maps to this
    definition. -/
structure ExternalNamesModel.Counter where
  n : U32

/-- A hand-written model for the opaque `external_names_split::incr`. -/
def ExternalNamesModel.incr (c : ExternalNamesModel.Counter) :
    Result ExternalNamesModel.Counter := do
  let n ← c.n + 1#u32
  ok ⟨n⟩

/-- A hand-written model for the trait `core::fmt::Write`, which
    `tests/external-names/external-names-traits.json` maps to this structure. It
    only models the required method `write_str`. -/
structure ExternalNamesModel.Write (Self : Type) where
  write_str : Self → Str → Result (core.result.Result Unit core.fmt.Error × Self)

/-- A hand-written model for `core::num::FpCategory`, which
    `tests/external-names/external-names-skipped.json` maps to this type. The
    entry leaves out the variant `Nan`: Aeneas names it as if the entry gave no
    variants, which is the name below. -/
inductive ExternalNamesModel.FpCategory where
  | Nan
  | Infinite
  | Zero
  | Subnormal
  | Normal

/-! The models which `tests/external-names/external-names-fields.json` maps the
    definitions of `external_names_fields` (and some of `core`) to. -/

/-- The model of `external_names_fields::tag`: it takes no type
    (`keep_params: [false]`) and is total (`can_fail: false`, `lift: false`). -/
def ExternalNamesModel.tag : U32 := 0#u32

/-- The model of `external_names_fields::first`: it takes no `Clone` instance
    (`keep_trait_clauses: [false]`). -/
def ExternalNamesModel.first {T : Type} (x : T) : Result T := ok x

/-- The model of the global `external_names_fields::LIMIT`, total
    (`can_fail: false`). -/
def ExternalNamesModel.limit : U32 := 10#u32

/-- The model of `external_names_fields::Tagged<T, U>`, which only takes `T`
    (`keep_params: [true, false]`). -/
structure ExternalNamesModel.Tagged (T : Type) where
  val : T

/-- The model of `core::ops::RangeToInclusive`: its field `end` is `hi`, and its
    constructor `make`. -/
structure ExternalNamesModel.UpTo (T : Type) where
  make ::
  hi : T

/-- The model of `core::task::Poll`, whose variants the entry names in full
    (`prefix_variant_names: false`). -/
inductive ExternalNamesModel.Poll (T : Type) where
  | ready (x : T)
  | pending

/-- The method `clone` of the implementation of `Clone` for `Poll`. -/
def ExternalNamesModel.clonePoll.clone {T : Type} (cloneInst : core.clone.Clone T) :
    ExternalNamesModel.Poll T → Result (ExternalNamesModel.Poll T)
  | .ready x => do
    let y ← cloneInst.clone x
    ok (.ready y)
  | .pending => ok .pending

/-- The model of the implementation of `Clone` for `Poll`. -/
def ExternalNamesModel.clonePoll {T : Type} (cloneInst : core.clone.Clone T) :
    core.clone.Clone (ExternalNamesModel.Poll T) := {
  clone := ExternalNamesModel.clonePoll.clone cloneInst
}

/-- The model of `core::fmt::Write`, with its required method and the provided
    `write_char`. -/
structure ExternalNamesModel.Writer (Self : Type) where
  write_str : Self → Str → Result (core.result.Result Unit core.fmt.Error × Self)
  write_char : Self → Char → Result (core.result.Result Unit core.fmt.Error × Self)

/-- The default implementation of `write_char`: the entry of `core::fmt::Write`
    lists it with `has_default: true`. Like the defaults which ship with
    Aeneas, it takes the instance of the trait. -/
@[trait_default]
def ExternalNamesModel.Writer.write_char.default {Self : Type}
    (_inst : ExternalNamesModel.Writer Self) (self : Self) (_c : Char) :
    Result (core.result.Result Unit core.fmt.Error × Self) :=
  ok (.Ok (), self)
