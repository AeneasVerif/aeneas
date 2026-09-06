import Aeneas.Tactic.Elab.TraitInst.Init

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

end Aeneas.TraitInst.Test
