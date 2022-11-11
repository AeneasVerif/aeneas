(** Define the global configuration options *)

(** {1 Interpreter} *)

(** Check that invariants are maintained whenever we execute a statement *)
let check_invariants = ref true

(** Expand all symbolic values containing borrows upon introduction - allows
    to use restrict ourselves to a simpler model for the projectors over
    symbolic values.
    The interpreter fails if doing this requires to do a branching (because
    we need to expand an enumeration with strictly more than one variant)
    or if we need to expand a recursive type (because this leads to looping).
 *)
let greedy_expand_symbolics_with_borrows = true

(** Experimental.

    TODO: remove (always true now)

    We sometimes want to temporarily break the invariant that there is no
    bottom value below a borrow. If this value is true, we don't check
    the invariant, and the rule becomes: we can't end a borrow *if* it contains
    a bottom value. The consequence is that it becomes ok to temporarily
    have bottom below a borrow, if we put something else inside before ending
    the borrow.

    For instance, when evaluating an assignment, we move the value which
    will be overwritten then do some administrative tasks with the borrows,
    then move the rvalue to its destination. We currently want to be able
    to check the invariants every time we end a borrow/an abstraction,
    meaning at intermediate steps of the assignment where the invariants
    might actually be broken.
 *)
let allow_bottom_below_borrow = true

(** If a function doesn't return any borrows, we can immediately call
    its backward functions. If this option is on, whenever we call a
    function *and* this function returns unit, we immediately end all the
    abstractions which are introduced and don't contain loans. This can be
    useful to make the code cleaner (the backward function is introduced
    where the function call happened) and make sure all forward functions
    with no return value are followed by a backward function.
 *)
let return_unit_end_abs_with_no_loans = true

(** {1 Translation} *)

(** Controls whether we need to use a state to model the external world
    (I/O, for instance).
 *)
let use_state = ref true (* TODO *)

(** Controls whether backward functions update the state, in case we use
    a state ({!use_state}).

    If they update the state, we generate code of the following style:
    {[
       (st1, y)  <-- f_fwd x st0; // st0 is the state upon calling f_fwd
       ...
       (st3, x') <-- f_back x st0 y' st2; // st2 is the state upon calling f_back
    ]}

    Otherwise, we generate code of the following shape:
    {[
       (st1, y)  <-- f_fwd x st0;
       ...
       x' <-- f_back x st0 y';
    ]}

    The second format is easier to reason about, but the first one is
    necessary to properly handle some Rust functions which use internal
    mutability such as
    {{:https://doc.rust-lang.org/std/cell/struct.RefCell.html#method.try_borrow_mut}[RefCell::try_mut_borrow]}:
    in order to model this behaviour we would need a state, and calling the backward
    function would update the state by reinserting the updated value in it.
 *)
let backward_no_state_update = ref false

(** Controls whether we split the generated definitions between different
    files for the types, clauses and functions, or if we group them in
    one file.
 *)
let split_files = ref true

(** If true, treat the unit functions (function taking no inputs and returning
    no outputs) as unit tests: evaluate them with the interpreter and check that
    they don't panic.
 *)
let test_unit_functions = ref false

(** If true, insert tests in the generated files to check that the
    unit functions normalize to [Success _].

    For instance, in F* it generates code like this:
    {[
      let _ = assert_norm (FUNCTION () = Success ())
    ]}
 *)
let test_trans_unit_functions = ref false

(** If [true], insert [decreases] clauses for all the recursive definitions.

    The body of such clauses must be defined by the user.
 *)
let extract_decreases_clauses = ref true

(** In order to help the user, we can generate "template" decrease clauses
    (i.e., definitions with proper signatures but dummy bodies) in a
    dedicated file.
 *)
let extract_template_decreases_clauses = ref false

(** {1 Micro passes} *)

(** Some provers like F* don't support the decomposition of return values
    in monadic let-bindings:
    {[
      // NOT supported in F*
      let (x, y) <-- f ();
      ...
    ]}

    In such situations, we might want to introduce an intermediate
    assignment:
    {[
      let tmp <-- f ();
      let (x, y) = tmp in
      ...
    ]}
 *)
let decompose_monadic_let_bindings = ref false

(** Controls the unfolding of monadic let-bindings to explicit matches:

    [y <-- f x; ...]

    becomes:

    [match f x with | Failure -> Failure | Return y -> ...]


    This is useful when extracting to F*: the support for monadic
    definitions is not super powerful.
    Note that when {!unfold_monadic_let_bindings} is true, setting
    {!decompose_monadic_let_bindings} to true and only makes the code
    more verbose.
 *)
let unfold_monadic_let_bindings = ref false

(** Controls whether we try to filter the calls to monadic functions
    (which can fail) when their outputs are not used.

    The useless calls are calls to backward functions which have no outputs.
    This case happens if the original Rust function only takes *shared* borrows
    as inputs, and is thus pretty common.

    We are allowed to do this only because in this specific case,
    the backward function fails *exactly* when the forward function fails
    (they actually do exactly the same thing, the only difference being
    that the forward function can potentially return a value), and upon
    reaching the place where we should introduce a call to the backward
    function, we know we have introduced a call to the forward function.

    Also note that in general, backward functions "do more things" than
    forward functions, and have more opportunities to fail (even though
    in the generated code, calls to the backward functions should fail
    exactly when the corresponding, previous call to the forward functions
    failed).

    This optimization is done in {!SymbolicToPure}.  We might want to move it to
    the micro-passes subsequent to the translation from symbolic to pure, but it
    is really super easy to do it when going from symbolic to pure. Note that
    we later filter the useless *forward* calls in the micro-passes, where it is
    more natural to do.

    See the comments for {!PureMicroPasses.expression_contains_child_call_in_all_paths}
    for additional explanations.
 *)
let filter_useless_monadic_calls = ref true

(** If {!filter_useless_monadic_calls} is activated, some functions
    become useless: if this option is true, we don't extract them.

    The calls to functions which always get filtered are:
    - the forward functions with unit return value
    - the backward functions which don't output anything (backward
      functions coming from rust functions with no mutable borrows
      as input values - note that if a function doesn't take mutable
      borrows as inputs, it can't return mutable borrows; we actually
      dynamically check for that).
 *)
let filter_useless_functions = ref true
