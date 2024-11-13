(** [external]: external function declarations *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Export External_Types.
Include External_Types.
Module External_FunsExternal.

Axiom core_cell_Cell_get :
  forall{T : Type} (markerCopyInst : core_marker_Copy_t T),
        core_cell_Cell_t T -> state -> result (state * T)
.

Axiom core_cell_Cell_get_mut :
  forall{T : Type},
        core_cell_Cell_t T -> state -> result (state * (T * (T -> state ->
          state * (core_cell_Cell_t T))))
.

End External_FunsExternal.
