open Types
open Values
open CfimAst
module V = Values

type binder = {
  index : VarId.id;  (** Unique variable identifier *)
  name : string option;  (** Possible name *)
}
[@@deriving show]
(** A binder used in an environment, to map a variable to a value *)

(** Environment value: mapping from variable to value, abstraction (only
    used in symbolic mode) or stack frame delimiter.
    
    TODO: rename? Environment element or something?
 *)
type env_value = Var of binder * typed_value | Abs of abs | Frame
[@@deriving show]

type env = env_value list [@@deriving show]

type interpreter_mode = ConcreteMode | SymbolicMode [@@deriving show]

type config = { mode : interpreter_mode; check_invariants : bool }
[@@deriving show]

type eval_ctx = {
  type_context : type_def list;
  fun_context : fun_def list;
  type_vars : type_var list;
  env : env;
  symbolic_counter : SymbolicValueId.generator;
  borrow_counter : BorrowId.generator;
}
[@@deriving show]
(** Evaluation context *)

let fresh_symbolic_value_id (ctx : eval_ctx) : eval_ctx * SymbolicValueId.id =
  let id, counter' = SymbolicValueId.fresh ctx.symbolic_counter in
  ({ ctx with symbolic_counter = counter' }, id)

let fresh_borrow_id (ctx : eval_ctx) : eval_ctx * BorrowId.id =
  let id, counter' = BorrowId.fresh ctx.borrow_counter in
  ({ ctx with borrow_counter = counter' }, id)

let lookup_type_var (ctx : eval_ctx) (vid : TypeVarId.id) : type_var =
  TypeVarId.nth ctx.type_vars vid

let ctx_lookup_binder (ctx : eval_ctx) (vid : VarId.id) : binder =
  (* TOOD: we might want to stop at the end of the frame *)
  let rec lookup env =
    match env with
    | [] ->
        raise (Invalid_argument ("Variable not found: " ^ VarId.to_string vid))
    | Var (var, _) :: env' -> if var.index = vid then var else lookup env'
    | (Abs _ | Frame) :: env' -> lookup env'
  in
  lookup ctx.env

let ctx_lookup_type_def (ctx : eval_ctx) (tid : TypeDefId.id) : type_def =
  TypeDefId.nth ctx.type_context tid

let ctx_lookup_fun_def (ctx : eval_ctx) (fid : FunDefId.id) : fun_def =
  FunDefId.nth ctx.fun_context fid

(** Retrieve a variable's value in an environment *)
let env_lookup_var_value (env : env) (vid : VarId.id) : typed_value =
  (* We take care to stop at the end of current frame: different variables
     in different frames can have the same id!
  *)
  let rec lookup env =
    match env with
    | [] -> failwith "Unexpected"
    | Var (var, v) :: env' -> if var.index = vid then v else lookup env'
    | Abs _ :: env' -> lookup env'
    | Frame :: _ -> failwith "End of frame"
  in
  lookup env

(** Retrieve a variable's value in an evaluation context *)
let ctx_lookup_var_value (ctx : eval_ctx) (vid : VarId.id) : typed_value =
  env_lookup_var_value ctx.env vid

(** Update a variable's value in an environment

    This is a helper function: it can break invariants and doesn't perform
    any check.
*)
let env_update_var_value (env : env) (vid : VarId.id) (nv : typed_value) : env =
  (* We take care to stop at the end of current frame: different variables
     in different frames can have the same id!
  *)
  let rec update env =
    match env with
    | [] -> failwith "Unexpected"
    | Var (var, v) :: env' ->
        if var.index = vid then Var (var, nv) :: env'
        else Var (var, v) :: update env'
    | Abs abs :: env' -> Abs abs :: update env'
    | Frame :: _ -> failwith "End of frame"
  in
  update env

let var_to_binder (var : var) : binder = { index = var.index; name = var.name }

(** Update a variable's value in an evaluation context.

    This is a helper function: it can break invariants and doesn't perform
    any check.
*)
let ctx_update_var_value (ctx : eval_ctx) (vid : VarId.id) (nv : typed_value) :
    eval_ctx =
  { ctx with env = env_update_var_value ctx.env vid nv }

(** Push a variable in the context's environment.

    Checks that the pushed variable and its value have the same type (this
    is important).
*)
let ctx_push_var (ctx : eval_ctx) (var : var) (v : typed_value) : eval_ctx =
  assert (var.var_ty = v.ty);
  let bv = var_to_binder var in
  { ctx with env = Var (bv, v) :: ctx.env }

(** Push a list of variables.

    Checks that the pushed variables and their values have the same type (this
    is important).
*)
let ctx_push_vars (ctx : eval_ctx) (vars : (var * typed_value) list) : eval_ctx
    =
  assert (List.for_all (fun (var, value) -> var.var_ty = value.ty) vars);
  let vars =
    List.map (fun (var, value) -> Var (var_to_binder var, value)) vars
  in
  let vars = List.rev vars in
  { ctx with env = List.append vars ctx.env }

let mk_bottom (ty : ety) : typed_value = { value = Bottom; ty }

(** Push an uninitialized variable (which thus maps to [Bottom]) *)
let ctx_push_uninitialized_var (ctx : eval_ctx) (var : var) : eval_ctx =
  ctx_push_var ctx var (mk_bottom var.var_ty)

(** Push a list of uninitialized variables (which thus map to [Bottom]) *)
let ctx_push_uninitialized_vars (ctx : eval_ctx) (vars : var list) : eval_ctx =
  let vars = List.map (fun v -> (v, mk_bottom v.var_ty)) vars in
  ctx_push_vars ctx vars

(** Visitor to iterate over the values in the current frame *)
class ['self] iter_frame_concrete =
  object (self : 'self)
    inherit [_] V.iter_typed_value

    method visit_env_value_Var : 'acc -> binder -> typed_value -> unit =
      fun acc vid v -> self#visit_typed_value acc v

    method visit_env : 'acc -> env -> unit =
      fun acc env ->
        match env with
        | [] -> ()
        | Var (vid, v) :: env ->
            self#visit_env_value_Var acc vid v;
            self#visit_env acc env
        | Abs _ :: _ -> failwith "Unexpected abstraction"
        | Frame :: _ -> (* We stop here *) ()
  end

(** Visitor to iterate over the values in the current frame *)
class ['self] map_frame_concrete =
  object (self : 'self)
    inherit [_] V.map_typed_value

    method visit_env_value_Var : 'acc -> binder -> typed_value -> env_value =
      fun acc vid v ->
        let v = self#visit_typed_value acc v in
        Var (vid, v)

    method visit_env : 'acc -> env -> env =
      fun acc env ->
        match env with
        | [] -> []
        | Var (vid, v) :: env ->
            let v = self#visit_env_value_Var acc vid v in
            let env = self#visit_env acc env in
            v :: env
        | Abs _ :: _ -> failwith "Unexpected abstraction"
        | Frame :: env -> (* We stop here *) Frame :: env
  end
