(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [external]: type definitions *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import External_TypesExternal.
Include External_TypesExternal.
Module External_Types.

(** Trait declaration: [core::marker::Copy]
    Source: '/rustc/library/core/src/marker.rs', lines 416:0-416:21
    Name pattern: core::marker::Copy *)
Record core_marker_Copy_t (Self : Type) := mkcore_marker_Copy_t {
  core_marker_Copy_tcore_marker_Copy_t_cloneCloneInst : core_clone_Clone Self;
}.

Arguments mkcore_marker_Copy_t { _ }.
Arguments core_marker_Copy_tcore_marker_Copy_t_cloneCloneInst { _ } _.

End External_Types.
