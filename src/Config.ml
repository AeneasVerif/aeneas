(** Define the global configuration options *)

(** {1 Backend choice} *)

(** The choice of backend *)
type backend = FStar | Coq | Lean | HOL4

let backend_names = [ "fstar"; "coq"; "rocq"; "lean"; "hol4" ]

(** Utility to compute the backend from an input parameter *)
let backend_of_string (b : string) : backend option =
  match b with
  | "fstar" | "FStar" -> Some FStar
  | "coq" | "Coq" | "rocq" | "Rocq" -> Some Coq
  | "lean" | "Lean" -> Some Lean
  | "hol4" | "HOL4" -> Some HOL4
  | _ -> None

let opt_backend : backend option ref = ref None

let set_backend (b : string) : unit =
  match backend_of_string b with
  | Some b -> opt_backend := Some b
  | None ->
      (* We shouldn't get there: the string should have been checked as
         belonging to the proper set *)
      raise (Failure "Unexpected")

(** Specify the namespace of the extract code.

    For instance, if the crate name is [foo] the namespace used for the
    extracted code will be [foo] but the user might want to use [Foo] instead.
*)
let namespace : string option ref = ref None

let set_namespace (s : string) : unit = namespace := Some s

(** Place the files inside a subdirectory in the destination.

    We use this to properly generate the import paths.

    For instance, when generating files for Lean, if the user wants to extract
    the files in the subdir [Foo/Code], the imports will have to be prefixed
    with [Foo.Code] (e.g., [import Foo.Code.Types]). *)
let subdir : string option ref = ref None

let set_subdir (s : string) : unit = subdir := Some s

(** If [true], we do not generate code and simply borrow-check the program
    instead. This allows us to relax some sanity checks which are present in the
    symbolic execution only to make sure we will be able to generate the pure
    translation.

    Remark: when checking if we are borrow-checking a program, checking this
    boolean or checking if [opt_backend] is [None] are equivalent. We need to
    have different variables for the purpose of implementing the parsing of the
    CI arguments. *)
let borrow_check = ref false

(** Get the target backend *)
let backend () : backend = Option.get !opt_backend

let if_backend (f : unit -> 'a) (default : 'a) : 'a =
  match !opt_backend with
  | None -> default
  | Some _ -> f ()

(** Print the source code span which emitted errors *)
let print_error_emitters = ref false

(** Print all the external definitions which are not listed in the builtin
    functions *)
let print_unknown_externals = ref false

(** {1 Interpreter} *)

(** Activate the sanity checks, and in particular the invariant checks that are
    performed at every evaluation step. This is very expensive (~100x slow down)
    but very efficient to catch mistakes early. *)
let sanity_checks = ref false

(** Expand all symbolic values containing borrows upon introduction - allows to
    use restrict ourselves to a simpler model for the projectors over symbolic
    values. The interpreter fails if doing this requires to do a branching
    (because we need to expand an enumeration with strictly more than one
    variant) or if we need to expand a recursive type (because this leads to
    looping). *)
let greedy_expand_symbolics_with_borrows = true

(** Experimental.

    TODO: remove (always true now), but check that when we panic/call a function
    there is no bottom below a borrow.

    We use this in two situations:

    1. We sometimes want to temporarily break the invariant that there is no
    bottom value below a *mutable* borrow. If this value is true, we don't check
    the invariant, and the rule becomes: we can't end a borrow *if* it contains
    a bottom value. The consequence is that it becomes ok to temporarily have
    bottom below a borrow, if we put something else inside before ending the
    borrow.

    For instance, when evaluating an assignment, we move the value which will be
    overwritten then do some administrative tasks with the borrows, then move
    the rvalue to its destination. We currently want to be able to check the
    invariants every time we end a borrow/an abstraction, meaning at
    intermediate steps of the assignment where the invariants might actually be
    broken.

    2. We sometimes need to join a value containing loans with a value
    containing bottoms. For instance, when joining:
    {[
      v -> bottom   U   v -> SL l 0
    ]}

    A problem is that we can't move [SL l 0] to a region abstraction or an
    anonymous values, because it is an **outer** loan: doing so would allow the
    loan to live indefinitely, and in particuler we would be allowed to
    overwrite [v] without ending it.

    A possibility is to force [l] to end, but then it might lead to a borrow
    checking issue later on, when trying to use the borrow [l]. Our solution is
    to use a shared loan containing the value bottom, leading to the following
    environment:

    {[
      v -> SL l' bottom
      abs { SB l', SL l 0 }
    ]}

    This way, the borrow [l] is preserved, but upon overwriting [v] we have to
    en [l'], which in turns requires ending [l]. We also can't *read* from [v],
    because after we ended the loan, [v] maps to [bottom] (we can only write to
    it). Also note that the shared borrow [l'] can't be used in any way (in
    particular, it can't be dereferenced).

    Finally, this solution works for mutable borrows/loans:
    {[
      v -> bottom   U   v -> ML l

        ~>

      v -> SL l' bottom
      abs { SB l', ML l }
    ]} *)
let allow_bottom_below_borrow = true

(** If a function doesn't return any borrows, we can immediately call its
    backward functions. If this option is on, whenever we call a function *and*
    this function returns unit, we immediately end all the abstractions which
    are introduced and don't contain loans. This can be useful to make the code
    cleaner (the backward function is introduced where the function call
    happened) and make sure all forward functions with no return value are
    followed by a backward function. *)
let return_unit_end_abs_with_no_loans = true

(** The maximum number of iterations we can do to find a loop fixed point.

    This is mostly for sanity: we should always find a fixed point in a
    reasonable number of iterations. If we fail to do so, it is likely a bug: we
    thus use this bound to detect a loop, fail and report the case to the user.
*)
let loop_fixed_point_max_num_iters = 2

(** {1 Translation} *)

(** Forbids using field projectors for structures.

    If we don't use field projectors, whenever we symbolically expand a
    structure value (note that accessing a structure field in the symbolic
    execution triggers its expansion), then instead of generating code like
    this:
    {[
      let x1 = s.f1 in
      let x2 = s.f2 in
      ...
    ]}

    we generate code like this:
    {[
      let Mkstruct x1 x2 ... = s in
      ...
    ]}

    Rem.: this used to be useful for Coq, because in Coq we can't define groups
    of mutually recursive records and inductives. In such cases, we extract the
    structures as inductives, which means that field projectors are not always
    available. As of today, we generate field projectors definitions (together
    with the appropriate notations). *)
let dont_use_field_projectors = ref false

(** Deconstructing ADTs which have only one variant with let-bindings is not
    always supported: this parameter controls whether we use let-bindings in
    such situations or not. *)
let always_deconstruct_adts_with_matches = ref false

(** Controls whether we use fuel to control termination. *)
let use_fuel = ref false

(** Controls whether we split the generated definitions between different files
    for the types, clauses and functions, or if we group them in one file. *)
let split_files = ref false

(** Only for Lean: generate the library entry point, if the crate is split
    between different files. The entry point is simply a file with the name of
    the crate and which includes all the other files. *)
let generate_lib_entry_point = ref false

(** For Lean, controls whether we generate a lakefile or not. *)
let lean_gen_lakefile = ref false

(** If true, treat the unit functions (function taking no inputs and returning
    no outputs) as unit tests: evaluate them with the interpreter and check that
    they don't panic. *)
let test_unit_functions = ref false

(** If true, insert tests in the generated files to check that the unit
    functions normalize to [Success _].

    For instance, in F* it generates code like this:
    {[
      let _ = assert_norm (FUNCTION () = Success ())
    ]} *)
let test_trans_unit_functions = ref false

(** If [true], use decreases clauses/termination measures for all the recursive
    definitions.

    More precisely:
    - for F*, we generate definitions which use decreases clauses
    - for Lean, we generate definitions which use termination measures and
      decreases proofs

    The body of such clauses/proofs must be defined by the user. *)
let extract_decreases_clauses = ref false

(** In order to help the user, we can generate "template" decrease clauses/
    termination measures (i.e., definitions with proper signatures but dummy
    bodies) in a dedicated file.

    We initialize it to [true], then deactivate it depending on the CL options
    given by the user. *)
let extract_template_decreases_clauses = ref true

(** {1 Micro passes} *)

(** Some provers like F* and Coq don't support the decomposition of return
    values in monadic let-bindings:
    {[
      (* NOT supported in F*/Coq *)
      (x, y) <-- f ();
      ...
    ]}

    In such situations, we might want to introduce an intermediate assignment:
    {[
      tmp <-- f ();
      let (x, y) = tmp in
      ...
    ]} *)
let decompose_monadic_let_bindings = ref false

(** Some provers like Coq don't support nested patterns in let-bindings:
    {[
      (* NOT supported in Coq *)
      (st, (x1, x2)) <-- f ();
      ...
    ]}

    In such situations, we might want to introduce intermediate assignments:
    {[
      (st, tmp) <-- f ();
      let (x1, x2) = tmp in
      ...
    ]} *)
let decompose_nested_let_patterns = ref false

(** Controls the unfolding of monadic let-bindings to explicit matches:

    [y <-- f x; ...]

    becomes:

    [match f x with | Failure -> Failure | Return y -> ...]

    This is useful when extracting to F*: the support for monadic definitions is
    not super powerful. Note that when {!unfold_monadic_let_bindings} is true,
    setting {!decompose_monadic_let_bindings} to true and only makes the code
    more verbose. *)
let unfold_monadic_let_bindings = ref false

(** Perform the following transformation:

    {[
      let y <-- f x   (* Must be an application, is not necessarily monadic *)
      let (a, b) := y (* Tuple decomposition *)
    ]}

    becomes:

    {[
      let (a, b) <-- f x
    ]} *)
let merge_let_app_decompose_tuple = ref false

(** Perform the following transformation:

    {[
      let y <-- ok e

            ~~>

      let y <-- toResult e
    ]}

    We only do this on a specific set of pure functions calls - those functions
    are identified in the "builtin" information about external function calls.
*)
let lift_pure_function_calls = ref false

(** Introduce calls to [massert] (monadic assertion).

    The pattern below is very frequent especially as it is introduced by the
    [assert!] macro. If the option is [true], we perform the following
    simplification:
    {[
      if b then e else fail ~~>massert b;
      e
    ]} *)
let intro_massert = ref true

(** Simplify the forward/backward functions, in case we merge them (i.e., the
    forward functions return the backward functions).

    The simplification occurs as follows:
    - if a forward function returns the unit type and has non-trivial backward
      functions, then we remove the returned output.
    - if a backward function doesn't have inputs, we evaluate it inside the
      forward function and don't wrap it in a result.

    Example:
    {[
      // LLBC:
      fn incr(x: &mut u32) { *x += 1 }

      // Translation without simplification:
      let incr (x : u32) : result (unit * result u32) = ...
                                   ^^^^   ^^^^^^
                                    |     remove this result
                                remove the unit

      // Translation with simplification:
      let incr (x : u32) : result u32 = ...
    ]} *)
let simplify_merged_fwd_backs = ref true

(** Use short names for the record fields.

    Some backends can't disambiguate records when their field names have
    collisions. When this happens, we use long names, by which we concatenate
    the record names with the field names, and check whether there are name
    collisions.

    For backends which can disambiguate records (typically by using the typing
    information), we use short names (i.e., the original field names). *)
let record_fields_short_names = ref false

(** Parameterize the traits with their associated types, so as not to use types
    as first class objects.

    This is useful for some backends with limited expressiveness like HOL4, and
    to account for type constraints (like
    [fn f<T : Foo>(...) where T::bar = usize]). *)
let parameterize_trait_types = ref false

(** For sanity check: type check the generated pure code (activates checks in
    several places).

    TODO: fix the bugs and reactivate *)
let type_check_pure_code = ref false

(** Shall we fail hard if we encounter an issue, or should we attempt to go as
    far as possible while leaving "holes" in the generated code? *)
let fail_hard = ref false

(** Shall we emit errors instead of warnings? *)
let warnings_as_errors = ref true

(** If true, add the type name as a prefix to the variant names. Ex.: In Rust:
    {[
      enum List = {
        Cons(u32, Box<List>),x
        Nil,
      }
    ]}

    F*, if option activated:
    {[
      type list =
      | ListCons : u32 -> list -> list
      | ListNil : list
    ]}

    F*, if option not activated:
    {[
      type list =
      | Cons : u32 -> list -> list
      | Nil : list
    ]} *)
let variant_concatenate_type_name = ref true

(** If true, extract the structures with unnamed fields as tuples.

    ex.:
    {[
      // Rust
      struct Foo(u32, u32)

      // OCaml
      type Foo = u32 * u32
    ]} *)
let use_tuple_structs = ref true

let backend_has_tuple_projectors backend =
  match backend with
  | Lean -> true
  | Coq | FStar | HOL4 -> false

(** Toggle the use of tuple projectors *)
let use_tuple_projectors = ref false

(** We we use nested projectors for tuple (like: [(0, 1).snd.fst]) or do we use
    better projector syntax? *)
let use_nested_tuple_projectors = ref false

(** Generate name patterns for the external definitions we encounter *)
let extract_external_name_patterns = ref true

(** *)
let match_patterns_with_trait_decl_refs = true

(** Decompose loops to recursive functions *)
let loops_to_recursive_functions = ref true

(** Should we run the translation in parallel? *)
let parallel = ref true
