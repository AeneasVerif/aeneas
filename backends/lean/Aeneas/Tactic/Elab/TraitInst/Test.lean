import Aeneas.Tactic.Elab.TraitInst.Init
import Aeneas.Tactic.Elab.TraitDefault.Init

namespace Aeneas.TraitInst.Test

/-! ## Test 1: Basic trait instance registration and lookup -/


/-

trait ToU32 {
  fn to_u32(&self) -> u32;
}

impl ToU32 for u32 {
  fn to_u32(&self) -> u32 {
    *u32
  }
}

structure ToU32 (Self : Type) where
  toU32 : Self → Result U32

def ToU32_U32 : ToU32 U32 := {
  toU32 := ...
}

impl clore::clone::Clone for alloc::vec::Vec<T> {
  ...
}

def core.clone.Clone_alloc'vec'Vec
def core.clone.Clone_Vec

impl clore::clone::Clone for MyType<alloc::vec::Vec<T>, ..> {
  ...
}

-/

namespace Test1

  structure MyTrait where
    val : Nat

  @[trait_inst {MyTrait for Foo}]
  def myTraitFooInst : MyTrait := { val := 42 }

  -- The pretty syntax should resolve to the definition
  #check {MyTrait for Foo}
  example : {MyTrait for Foo} = myTraitFooInst := rfl

end Test1

/-! ## Test 2: Dotted names -/

namespace Test2

  structure core.clone.Clone where
    clone_val : Nat

  structure alloc.vec.Vec where
    data : List Nat

  @[trait_inst {core.clone.Clone for alloc.vec.Vec<_>}]
  def alloc_vec_Clone_inst : core.clone.Clone := { clone_val := 0 }

  #check {core.clone.Clone for alloc.vec.Vec<_>}
  example : {core.clone.Clone for alloc.vec.Vec<_>} = alloc_vec_Clone_inst := by rfl

  open core.clone in
  open alloc.vec in
  #check {Clone for Vec<_>}
  example : {core.clone.Clone for alloc.vec.Vec<_>} = alloc_vec_Clone_inst := by rfl

  namespace core.clone
    #check {Clone for alloc.vec.Vec<_>}
    example : {core.clone.Clone for alloc.vec.Vec<_>} = alloc_vec_Clone_inst := by rfl
  end core.clone

end Test2

/-! ## Test 3: Trait with type arguments -/

namespace Test3

  structure Foo where
    val : Nat

  structure Type0 where
  structure Type1 where
  structure Bar where

  @[trait_inst {Foo<Type0, Type1> for Bar}]
  def fooBarInst : Foo := { val := 7 }

  #check {Foo<Type0, Type1> for Bar}
  example : {Foo<Type0, Type1> for Bar} = fooBarInst := rfl

end Test3

/-! ## Test 4: Tuple self type -/

namespace Test4

  structure Clone where
    val : Nat

  structure A where
  structure B where

  @[trait_inst {Clone for (A, B)}]
  def cloneTupleInst : Clone := { val := 0 }

  #check {Clone for (A, B)}
  example : {Clone for (A, B)} = cloneTupleInst := rfl

end Test4

/-! ## Test 5: Slice type -/

namespace Test5

  structure Clone where
    val : Nat

  structure U8 where

  @[trait_inst {Clone for Slice<U8>}]
  def cloneSliceInst : Clone := { val := 1 }

  #check {Clone for Slice<U8>}
  example : {Clone for Slice<U8>} = cloneSliceInst := rfl

end Test5

/-! ## Test 6: Array type with concrete size -/

namespace Test6

  structure Clone where
    val : Nat

  structure U8 where

  @[trait_inst {Clone for Array<U8, 32>}]
  def cloneArrayInst : Clone := { val := 2 }

  #check {Clone for Array<U8, 32>}
  example : {Clone for Array<U8, 32>} = cloneArrayInst := rfl

end Test6

/-! ## Test 7: Array type with wildcard size -/

namespace Test7

  structure Clone where
    val : Nat

  structure U8 where

  @[trait_inst {Clone for Array<U8, _>}]
  def cloneArrayWildInst : Clone := { val := 3 }

  #check {Clone for Array<U8, _>}
  example : {Clone for Array<U8, _>} = cloneArrayWildInst := rfl

end Test7

/-! ## Test 8: Namespace resolution -/

namespace Test8

  namespace my.traits
    structure MyTrait where
      val : Nat
  end my.traits

  structure MyType where

  @[trait_inst {my.traits.MyTrait for MyType}]
  def myTypeTraitInst : my.traits.MyTrait := { val := 99 }

  -- Using full name works
  #check {my.traits.MyTrait for MyType}

  -- Using short name with open namespace should also work
  open my.traits in
  #check {MyTrait for MyType}

end Test8

/-! ## Test 9: Nested type arguments -/

namespace Test9

  structure Hash where
    val : Nat

  structure Map where
  structure Str where
  structure Vec where

  /- `>>` is properly split — no space needed between closing angle brackets -/
  @[trait_inst {Hash for Map<Str, Vec<_>>}]
  def hashMapStrVecInst : Hash := { val := 5 }

  #check {Hash for Map<Str, Vec<_>>}
  example : {Hash for Map<Str, Vec<_>>} = hashMapStrVecInst := by rfl

end Test9

/-! ## Test 10: Dot notation — projection and application

The extraction pipeline prints trait method calls as `{Trait for Type}.method args`,
so the trailing projection parser must attach to the notation term. -/

namespace Test10

  structure MyTrait (Self : Type) where
    get_val : Self → Nat

  structure Foo where
    x : Nat

  @[trait_inst {MyTrait for Foo}]
  def myTraitFooInst : MyTrait Foo := { get_val := fun f => f.x }

  -- Field projection attaches directly to the notation
  #check {MyTrait for Foo}.get_val
  example : {MyTrait for Foo}.get_val ⟨3⟩ = 3 := rfl

  -- Application through the projection
  example (f : Foo) : {MyTrait for Foo}.get_val f = f.x := rfl

  -- Parenthesized form (what extraction emits)
  example (f : Foo) : ({MyTrait for Foo}).get_val f = f.x := rfl
  example (f : Foo) : ({MyTrait for Foo}.get_val f) = f.x := rfl

end Test10

/-! ## Test 11: Notation as a record field value and in anonymous constructors -/

namespace Test11

  structure Clone (Self : Type) where
    clone : Self → Self

  structure A where

  @[trait_inst {Clone for A}]
  def cloneA : Clone A := { clone := id }

  structure Wrapper where
    cloneInst : Clone A

  -- Structure-instance field value (extraction emits parent clauses this way)
  def w : Wrapper := { cloneInst := {Clone for A} }

  -- Anonymous constructor
  def w' : Wrapper := ⟨{Clone for A}⟩

  example : w.cloneInst = cloneA := rfl
  example : w'.cloneInst = cloneA := rfl

end Test11

/-! ## Test 12: do-notation positions

At the *start* of a do-sequence (after `do`, `then`, `else`, `=>`), a bare `{`
commits the parser to a bracketed do-block (`doSeqBracketed`), so
`do {MyTrait for Foo}.get_val f` fails with "expected 'in'". The extraction
always parenthesizes notation-headed terms, which works in every position. -/

namespace Test12

  structure MyTrait (Self : Type) where
    get_val : Self → Option Nat

  structure Foo where

  @[trait_inst {MyTrait for Foo}]
  def myTraitFooInst : MyTrait Foo := { get_val := fun _ => some 0 }

  -- Parenthesized at do-sequence start: OK
  def ok1 (f : Foo) : Option Nat := do
    ({MyTrait for Foo}).get_val f

  def ok2 (f : Foo) : Option Nat := do
    ({MyTrait for Foo}.get_val f)

  -- On a bind's rhs the conflict does not arise, even unparenthesized
  def ok3 (f : Foo) : Option Nat := do
    let x ← {MyTrait for Foo}.get_val f
    pure x

  -- `if then else` branches are do-sequence starts too
  def ok4 (f : Foo) (b : Bool) : Option Nat := do
    if b then ({MyTrait for Foo}).get_val f
    else ({MyTrait for Foo}.get_val f)

end Test12

/-! ## Test 13: Parameterized instances — positional application -/

namespace Test13

  structure Clone (Self : Type) where
    clone : Self → Self

  structure Vec (T : Type) where
    data : List T

  @[trait_inst {Clone for Vec<_>}]
  def cloneVec (T : Type) (cloneT : Clone T) : Clone (Vec T) :=
    { clone := fun v => { data := v.data.map cloneT.clone } }

  @[trait_inst {Clone for Nat}]
  def cloneNat : Clone Nat := { clone := id }

  -- The notation resolves to the (un-applied) constant; positional application
  -- and projection compose around it
  #check ({Clone for Vec<_>} Nat {Clone for Nat}).clone
  example (v : Vec Nat) :
      ({Clone for Vec<_>} Nat {Clone for Nat}).clone v = ⟨v.data.map id⟩ := rfl

end Test13

/-! ## Test 14: Combined attribute lists and `impl_def` -/

namespace Test14

  structure Trait (Self : Type) where
    f : Self → Nat

  structure T where

  -- `trait_inst` combined with other attributes in one list
  @[reducible, trait_inst {Trait for T}]
  def traitT : Trait T := { f := fun _ => 0 }

  #check {Trait for T}
  example : {Trait for T} = traitT := rfl

  -- `trait_inst` on an `impl_def` (used for self-referential impls)
  structure Trait2 (Self : Type) where
    g : Self → Nat

  @[reducible, trait_inst {Trait2 for T}]
  impl_def trait2T : Trait2 T := { g := fun _ => 0 }

  #check {Trait2 for T}
  example : {Trait2 for T} = trait2T := rfl
  example : {Trait2 for T}.g ⟨⟩ = 0 := rfl

end Test14

/-! ## Test 15: Pattern variables from binder names

Identifiers in the registered pattern which match a ∀-binder of the definition
become pattern variables. Repeated pattern variables must bind consistently. -/

namespace Test15

  structure Convert (Self : Type) (Target : Type) where
    convert : Self → Target

  structure Wrap (T : Type) where
    val : T

  @[trait_inst {Convert<T> for Wrap<T>}]
  def convertWrap (T : Type) : Convert (Wrap T) T := { convert := fun w => w.val }

  -- Underspecified queries match the pattern
  #check {Convert<_> for Wrap<_>}
  example : {Convert<_> for Wrap<_>} = convertWrap := rfl
  -- Omitting the trait argument list is equivalent to all-holes
  example : {Convert for Wrap<_>} = convertWrap := rfl

  -- A blanket impl: the self type itself is a pattern variable
  structure Id' (Self : Type) where
    this : Self → Self

  @[trait_inst {Id' for T}]
  def idBlanket (T : Type) : Id' T := { this := id }

  #check {Id' for _}
  example : {Id' for _} = idBlanket := rfl

end Test15

/-! ## Test 16: Const-generic literal arguments -/

namespace Test16

  structure WithLen (Self : Type) (LEN : Nat) where
    len_val : Nat

  structure Buf where

  @[trait_inst {WithLen<32> for Buf}]
  def withLenBuf : WithLen Buf 32 := { len_val := 32 }

  #check {WithLen<32> for Buf}
  example : {WithLen<32> for Buf} = withLenBuf := rfl
  -- A hole in the literal position also matches
  example : {WithLen<_> for Buf} = withLenBuf := rfl

  -- A different literal does not match: registrations for different lengths
  -- can coexist
  @[trait_inst {WithLen<64> for Buf}]
  def withLenBuf64 : WithLen Buf 64 := { len_val := 64 }

  example : {WithLen<64> for Buf} = withLenBuf64 := rfl
  example : {WithLen<32> for Buf} = withLenBuf := rfl

end Test16

/-! ## Test 17: Instantiation of concrete queries

A fully concrete query elaborates the type arguments, and recursively
resolves the clause parameters of the implementation through the registry. -/

namespace Test17

  @[trait_decl]
  structure Clone (Self : Type) where
    clone : Self → Self

  structure Vec (T : Type) where
    data : List T

  @[trait_inst {Clone for Nat}]
  def cloneNat : Clone Nat := { clone := id }

  @[trait_inst {Clone for Vec<T>}]
  def cloneVec (T : Type) (cloneT : Clone T) : Clone (Vec T) :=
    { clone := fun v => { data := v.data.map cloneT.clone } }

  -- Type arguments are elaborated and the `Clone Nat` clause is resolved
  -- through the registry
  example : {Clone for Vec<Nat>} = cloneVec Nat cloneNat := rfl
  -- Nested instantiation
  example : {Clone for Vec<Vec<Nat>>}
      = cloneVec (Vec Nat) (cloneVec Nat cloneNat) := rfl

  -- No method definition `cloneVec.clone`: `.clone` falls back to a record
  -- projection
  example (v : Vec Nat) :
      {Clone for Vec<Nat>}.clone v = (cloneVec Nat cloneNat).clone v := rfl

  -- Delaboration: applications of registered implementations print with the
  -- notation, with the pattern variables instantiated
  /-- info: {Clone for Vec<Nat>} : Clone (Vec Nat) -/
  #guard_msgs in
  #check (cloneVec Nat cloneNat)

end Test17

/-! ## Test 18: Method name-join

When the trait instance resolves to a top-level implementation `C` and a
constant `C.f` exists (the extraction generates the methods of an impl as
standalone definitions), `{...}.f` elaborates to `C.f` applied to the
implementation's arguments — the exact term shape of the direct calls the
extraction generates. -/

namespace Test18

  @[trait_decl]
  structure Clone (Self : Type) where
    clone : Self → Self

  structure Vec (T : Type) where
    data : List T

  @[trait_inst {Clone for Nat}]
  def cloneNat : Clone Nat := { clone := id }

  def cloneVec.clone (T : Type) (_cloneT : Clone T) (v : Vec T) : Vec T := v

  @[trait_inst {Clone for Vec<T>}]
  def cloneVec (T : Type) (cloneT : Clone T) : Clone (Vec T) :=
    { clone := cloneVec.clone T cloneT }

  -- `{Clone for Vec<Nat>}.clone` elaborates to the method *definition*
  -- applied to the implementation's arguments (not a record projection)
  example (v : Vec Nat) :
      {Clone for Vec<Nat>}.clone v = cloneVec.clone Nat cloneNat v := rfl

  -- Method applications delaborate back to the notation
  /-- info: {Clone for Vec<Nat>}.clone : Vec Nat → Vec Nat -/
  #guard_msgs in
  #check cloneVec.clone Nat cloneNat

end Test18

/-! ## Test 19: Local context search

References to clauses in scope: `{Trait for T}` finds a hypothesis of type
`Trait T`, including transitively through the parent-clause fields of the
trait instances in scope. Requires the trait structures to be marked with
`@[trait_decl]`. -/

namespace Test19

  @[trait_decl]
  structure Clone (Self : Type) where
    clone : Self → Self

  @[trait_decl]
  structure Trait (Self : Type) where
    cloneInst : Clone Self
    f : Self → Nat

  -- Direct clause
  example {T : Type} (CloneInst : Clone T) : {Clone for T} = CloneInst := rfl
  example {T : Type} (CloneInst : Clone T) (x : T) : T :=
    {Clone for T}.clone x

  -- Through a parent-clause field
  example {T : Type} (TraitInst : Trait T) :
      {Clone for T} = TraitInst.cloneInst := rfl
  example {T : Type} (TraitInst : Trait T) (x : T) : T :=
    {Clone for T}.clone x

  -- A direct hypothesis shadows the parent-clause fields (shallower depth)
  example {T : Type} (_TraitInst : Trait T) (CloneInst : Clone T) :
      {Clone for T} = CloneInst := rfl

  -- A local clause shadows a registered (blanket) instance
  @[trait_inst {Trait for T}]
  def blanketTrait (T : Type) (cloneT : Clone T) : Trait T :=
    { cloneInst := cloneT, f := fun _ => 0 }

  example {T : Type} (TraitInst : Trait T) : {Trait for T} = TraitInst := rfl

  -- The blanket instance applies when no local clause matches, with its
  -- clause resolved from the local context
  example {T : Type} (CloneInst : Clone T) :
      {Trait for T} = blanketTrait T CloneInst := rfl

end Test19

end Aeneas.TraitInst.Test
