(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [matches] *)
module Matches
open Primitives

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [matches::match_u32]:
    Source: 'tests/src/matches.rs', lines 4:0-10:1 *)
let match_u32 (x : u32) : result u32 =
  begin match x with | 0 -> Ok 0 | 1 -> Ok 1 | _ -> Ok 2 end

