-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [issue_270_loop_list]
import Aeneas
open Aeneas.Std Result Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace issue_270_loop_list

/- [issue_270_loop_list::List]
   Source: 'tests/src/issue-270-loop-list.rs', lines 2:0-5:1 -/
inductive List (T : Type) where
| Cons : T → List T → List T
| Nil : List T

/- [issue_270_loop_list::foo]: loop 0:
   Source: 'tests/src/issue-270-loop-list.rs', lines 10:8-12:9 -/
def foo_loop (t : List (List U8)) : Result Unit :=
  match t with
  | List.Cons _ tt => foo_loop tt
  | List.Nil => ok ()
partial_fixpoint

/- [issue_270_loop_list::foo]:
   Source: 'tests/src/issue-270-loop-list.rs', lines 7:0-14:1 -/
def foo (v : List (List U8)) : Result Unit :=
  match v with
  | List.Cons l t => foo_loop t
  | List.Nil => ok ()

end issue_270_loop_list
