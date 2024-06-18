-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [rename_attribute]
import Base
open Primitives
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace rename_attribute

/- Trait declaration: [rename_attribute::BoolTrait]
   Source: 'tests/src/rename_attribute.rs', lines 7:0-7:19 -/
structure BoolTest (Self : Type) where
  getTest : Self → Result Bool

/- [rename_attribute::{(rename_attribute::BoolTrait for bool)}::get_bool]:
   Source: 'tests/src/rename_attribute.rs', lines 21:4-21:30 -/
def BoolTraitBool.getTest (self : Bool) : Result Bool :=
  Result.ok self

/- Trait implementation: [rename_attribute::{(rename_attribute::BoolTrait for bool)}]
   Source: 'tests/src/rename_attribute.rs', lines 20:0-20:23 -/
def BoolImpl : BoolTest Bool := {
  getTest := BoolTraitBool.getTest
}

/- [rename_attribute::BoolTrait::ret_true]:
   Source: 'tests/src/rename_attribute.rs', lines 14:4-14:30 -/
def BoolTrait.retTest
  {Self : Type} (self_clause : BoolTest Self) (self : Self) : Result Bool :=
  Result.ok true

/- [rename_attribute::test_bool_trait]:
   Source: 'tests/src/rename_attribute.rs', lines 27:0-27:42 -/
def BoolFn (T : Type) (x : Bool) : Result Bool :=
  do
  let b ← BoolTraitBool.getTest x
  if b
  then BoolTrait.retTest BoolImpl x
  else Result.ok false

/- [rename_attribute::SimpleEnum]
   Source: 'tests/src/rename_attribute.rs', lines 35:0-35:15 -/
inductive VariantsTest :=
| Variant1 : VariantsTest
| SecondVariant : VariantsTest
| ThirdVariant : VariantsTest

/- [rename_attribute::Foo]
   Source: 'tests/src/rename_attribute.rs', lines 43:0-43:10 -/
structure StructTest where
  FieldTest : U32

/- [rename_attribute::C]
   Source: 'tests/src/rename_attribute.rs', lines 49:0-49:12 -/
def Const_Test_body : Result U32 := do
                                    let i ← 100#u32 + 10#u32
                                    i + 1#u32
def Const_Test : U32 := eval_global Const_Test_body

/- [rename_attribute::CA]
   Source: 'tests/src/rename_attribute.rs', lines 52:0-52:13 -/
def Const_Aeneas11_body : Result U32 := 10#u32 + 1#u32
def Const_Aeneas11 : U32 := eval_global Const_Aeneas11_body

/- [rename_attribute::factorial]:
   Source: 'tests/src/rename_attribute.rs', lines 55:0-55:27 -/
divergent def Factfn (n : U64) : Result U64 :=
  if n <= 1#u64
  then Result.ok 1#u64
  else do
       let i ← n - 1#u64
       let i1 ← Factfn i
       n * i1

/- [rename_attribute::sum]: loop 0:
   Source: 'tests/src/rename_attribute.rs', lines 64:0-64:27 -/
divergent def No_borrows_sum_loop
  (max : U32) (i : U32) (s : U32) : Result U32 :=
  if i < max
  then do
       let s1 ← s + i
       let i1 ← i + 1#u32
       No_borrows_sum_loop max i1 s1
  else s * 2#u32

/- [rename_attribute::sum]:
   Source: 'tests/src/rename_attribute.rs', lines 64:0-64:27 -/
def No_borrows_sum (max : U32) : Result U32 :=
  No_borrows_sum_loop max 0#u32 0#u32

end rename_attribute
