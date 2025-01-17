-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [bst]: type definitions
import Base
open Primitives
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace bst

/- [bst::Ordering]
   Source: 'src/bst.rs', lines 5:0-9:1 -/
inductive Ordering where
| Less : Ordering
| Equal : Ordering
| Greater : Ordering

/- Trait declaration: [bst::Ord]
   Source: 'src/bst.rs', lines 11:0-13:1 -/
structure Ord (Self : Type) where
  cmp : Self → Self → Result Ordering

/- [bst::Node]
   Source: 'src/bst.rs', lines 15:0-19:1 -/
inductive Node (T : Type) where
| mk : T → Option (Node T) → Option (Node T) → Node T

def Node.value {T : Type} (x : Node T) := match x with | Node.mk x1 _ _ => x1

def Node.left {T : Type} (x : Node T) := match x with | Node.mk _ x1 _ => x1

def Node.right {T : Type} (x : Node T) := match x with | Node.mk _ _ x1 => x1

@[simp]
theorem Node.value._simpLemma_ {T : Type} (value : T) (left : Option (Node T))
  (right : Option (Node T)) : (Node.mk value left right).value = value :=
  by rfl

@[simp]
theorem Node.left._simpLemma_ {T : Type} (value : T) (left : Option (Node T))
  (right : Option (Node T)) : (Node.mk value left right).left = left := by rfl

@[simp]
theorem Node.right._simpLemma_ {T : Type} (value : T) (left : Option (Node T))
  (right : Option (Node T)) : (Node.mk value left right).right = right :=
  by rfl

/- [bst::TreeSet]
   Source: 'src/bst.rs', lines 23:0-25:1 -/
structure TreeSet (T : Type) where
  root : Option (Node T)

end bst
