(** [hashmap]: external types. *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import List.
Import ListNotations.
Local Open Scope Primitives_scope.
Module Hashmap_TypesExternal.

(** The state type used in the state-error monad *)
Axiom state : Type.

End Hashmap_TypesExternal.
