import Lean

namespace Aeneas.Std.ElabScalar

open Lean Elab Command Term Meta

/- Generic scalar term -/
declare_syntax_cat gscalar_ident
scoped syntax ident : gscalar_ident
scoped syntax "%S" : gscalar_ident
scoped syntax gscalar_ident "." ident : gscalar_ident

/- Using the same precedences as in `Lean.Notation` -/
declare_syntax_cat gscalar_term
scoped syntax num : gscalar_term
scoped syntax:max "-" gscalar_term : gscalar_term
scoped syntax:65 gscalar_term:65 " + " gscalar_term:66 : gscalar_term
scoped syntax:65 gscalar_term:65 " - " gscalar_term:66 : gscalar_term
scoped syntax:65 gscalar_term:65 " * " gscalar_term:66 : gscalar_term
scoped syntax:65 gscalar_term:65 " / " gscalar_term:66 : gscalar_term
scoped syntax:65 gscalar_term:65 " % " gscalar_term:66 : gscalar_term
scoped syntax:1024 gscalar_term:50 " = " gscalar_term:50 : gscalar_term
scoped syntax:50 gscalar_term:50 " ≤ " gscalar_term:50 : gscalar_term
scoped syntax:50 gscalar_term:50 " < " gscalar_term:50 : gscalar_term
scoped syntax:50 gscalar_term:50 " ≥ " gscalar_term:50 : gscalar_term
scoped syntax:50 gscalar_term:50 " > " gscalar_term:50 : gscalar_term
scoped syntax:35 gscalar_term:36 " ∧ " gscalar_term:35 : gscalar_term
scoped syntax:30 gscalar_term:31 " ∨ " gscalar_term:50 : gscalar_term
scoped syntax:max "¬ " gscalar_term : gscalar_term

declare_syntax_cat gscalar_arg
scoped syntax gscalar_ident : gscalar_arg
scoped syntax num : gscalar_arg
scoped syntax "(" gscalar_term ")" : gscalar_arg

--scoped syntax gscalar_term gscalar_arg : gscalar_term
-- TODO: what is the precedence of function application?
scoped syntax:100 gscalar_term:100 gscalar_term:101 : gscalar_term

-- For now we harcode a specific kind of matches
scoped syntax "match" gscalar_term "with" "|" term "=>" gscalar_term "|" term "=>" gscalar_term : gscalar_term

scoped syntax gscalar_ident : gscalar_term

declare_syntax_cat gscalar_param
scoped syntax "(" ident+ ":" gscalar_term ")" : gscalar_param
scoped syntax "{" ident+ ":" gscalar_term "}" : gscalar_param

partial def elabGScalarIdent (scalarTy : Name) (stx : TSyntax `gscalar_ident) : CommandElabM Name := do
  println! "elabGScalarIdent: {stx}"
  match stx with
  | `(gscalar_ident|%S) => pure scalarTy
  | `(gscalar_ident|$id:ident) => pure id.getId
  | `(gscalar_ident| $id0 . $id1:ident) => do
    let id0 ← elabGScalarIdent scalarTy id0
    pure (id0 ++ id1.getId)
  | _ => throwUnsupportedSyntax

mutual
partial def elabGScalarTerm (scalarTy : Name) (stx : TSyntax `gscalar_term) : CommandElabM (TSyntax `term) := do
  println! "elabGScalarTerm: {stx}"
  let elabTerm := elabGScalarTerm scalarTy
  match stx with
  | `(gscalar_term| $x $y) => `(term| $(← elabTerm x) $(← elabTerm y))
  | `(gscalar_term| $x:num) => `(term| $x)
  | `(gscalar_term| - $x) => `(term| - $(← elabTerm x))
  | `(gscalar_term| $x + $y) => `(term| $(← elabTerm x) + $(← elabTerm y))
  | `(gscalar_term| $x - $y) => `(term| $(← elabTerm x) - $(← elabTerm y))
  | `(gscalar_term| $x * $y) => `(term| $(← elabTerm x) * $(← elabTerm y))
  | `(gscalar_term| $x / $y) => `(term| $(← elabTerm x) / $(← elabTerm y))
  | `(gscalar_term| $x % $y) => `(term| $(← elabTerm x) % $(← elabTerm y))
  | `(gscalar_term| $x = $y) => `(term| $(← elabTerm x) = $(← elabTerm y))
  | `(gscalar_term| $x ≤ $y) => `(term| $(← elabTerm x) ≤ $(← elabTerm y))
  | `(gscalar_term| $x < $y) => `(term| $(← elabTerm x) < $(← elabTerm y))
  | `(gscalar_term| $x ≥ $y) => `(term| $(← elabTerm x) ≥ $(← elabTerm y))
  | `(gscalar_term| $x > $y) => `(term| $(← elabTerm x) > $(← elabTerm y))
  | `(gscalar_term| $x ∧ $y) => `(term| $(← elabTerm x) ∧ $(← elabTerm y))
  | `(gscalar_term| ¬ $x) => `(term| ¬ $(← elabTerm x))
  | `(gscalar_term| match $scrut with | $y => $e1 | $z => $e2 ) => do
    -- We only support a specific kind of matches
    println! "elabGScalarTerm: match: y: {y}"
    let y: TSyntax `ident ← match y with
      | `(some $y:ident) => pure y
      | _ => throwUnsupportedSyntax
    println! "elabGScalarTerm: match: z: {z}"
    let _ ← match z with
      | `(none) => pure ()
      | _ => throwUnsupportedSyntax
    println! "elabGScalarTerm: match: e1: {e1}"
    let e1 ← elabTerm e1
    println! "elabGScalarTerm: match: e2: {e2}"
    let e2 ← elabTerm e2
    println! "elabGScalarTerm: match: scrut: {scrut}"
    let scrut ← elabTerm scrut
    `(term| match $scrut:term with | some $y => $e1 | none => $e2)
  | `($_) => do
    -- Should be an ident
    println! "elabGScalarTerm: ident: {stx}"
    let id ← elabGScalarIdent scalarTy ⟨stx.raw[0]!⟩
    pure (mkIdent id)


partial def elabGScalarArg (scalarTy : Name) (stx : TSyntax `gscalar_arg) : CommandElabM (TSyntax `term) := do
  println! "elabGScalarArg: {stx}"
  let elabTerm := elabGScalarTerm scalarTy
  match stx with
  | `(gscalar_arg|$x:num) => `(term|$x)
  | `(gscalar_arg|($x)) => `(term|($(← elabTerm x)))
  | `($_) =>
    -- Should be an ident
    println! "elabGScalarArg: ident: {stx}"
    let id ← elabGScalarIdent scalarTy ⟨stx.raw[0]!⟩
    pure (mkIdent id)

end

partial def elabGScalarParams (scalarTy : Name) (stx : TSyntax `gscalar_param) :
  CommandElabM (TSyntax `Lean.Parser.Term.bracketedBinder) := do
  match stx with
  | `(gscalar_param| ($ids* : $ty)) =>
    let ty ← elabGScalarTerm scalarTy ty
    `(bracketedBinder|($(ids)* : $ty))
  | `(gscalar_param| {$ids* : $ty}) =>
    let ty ← elabGScalarTerm scalarTy ty
    `(bracketedBinder|{$(ids)* : $ty})
  | _ => throwUnsupportedSyntax

syntax (name := uscalar_def1) "#uscalar_def1" ident "(" gscalar_term ")" term : command

@[command_elab uscalar_def1]
def uscalarDef1Impl : CommandElab := fun stx => do
  logInfo ("#uscalar_def (stx): " ++ stx)
  match stx with
  | `(#uscalar_def1 $id ($args) $body) =>
    logInfo m!"#uscalar_def: {id} {body}"
    let args ← elabGScalarTerm ``U8 args
    let stx : TSyntax `command ← `(def $id := $args)
    elabDeclaration stx
  | _ => throwUnsupportedSyntax

syntax (name := uscalarDef) "uscalar_def" gscalar_ident gscalar_param+ ":" gscalar_term ":=" term : command
syntax (name := uscalarThm) "uscalar_theorem" gscalar_ident gscalar_param+ ":" gscalar_term ":=" term : command
--syntax (name := uscalarThmBy) "uscalar_theorem" gscalar_ident gscalar_param+ ":" gscalar_term ":=" "by" tactic : command

@[command_elab uscalarDef]
def uscalarDefImpl : CommandElab := fun stx => do
  logInfo ("uscalar_def (stx): " ++ stx)
  match stx with
  | `(uscalarDef| uscalar_def $id $args* : $ty := $body) =>
    logInfo m!"uscalar_def: {id} {args} : {ty} := {body}"
    let scalarTy := `U8
    let id ← elabGScalarIdent scalarTy id
    let args ← args.mapM (elabGScalarParams scalarTy)
    let ty ← elabGScalarTerm scalarTy ty
    let stx : TSyntax `command ← `(def $(mkIdent id) $(args)* : $ty := $body)
    elabDeclaration stx
  | _ => throwUnsupportedSyntax

/-@[command_elab uscalarThm]
def uscalarThmImpl : CommandElab := fun stx => do
  logInfo ("uscalar_thm (stx): " ++ stx)
  match stx with
  | `(uscalarThm| uscalar_theorem $id $args* : $ty := $body) =>
    logInfo m!"uscalar_thm: {id} {args} : {ty} := {body}"
    let scalarTy := `U8
    let id ← elabGScalarIdent scalarTy id
    let args ← args.mapM (elabGScalarParams scalarTy)
    let ty ← elabGScalarTerm scalarTy ty
    let stx : TSyntax `command ← `(theorem $(mkIdent id) $(args)* : $ty := $body)
    logInfo m!"Final declaration:\n{stx}"
    elabDeclaration stx
  | _ => throwUnsupportedSyntax-/

@[command_elab uscalarThm]
def uscalarThmByImpl : CommandElab := fun stx => do
  logInfo ("uscalar_thm (stx): " ++ stx)
  match stx with
  | `(uscalarThm| uscalar_theorem $id $args* : $ty := by $body) =>
    logInfo m!"uscalar_thm: {id} {args} : {ty} := {body}"
    let scalarTy := `U8
    let id ← elabGScalarIdent scalarTy id
    let args ← args.mapM (elabGScalarParams scalarTy)
    let ty ← elabGScalarTerm scalarTy ty
    let stx : TSyntax `command ← `(theorem $(mkIdent id) $(args)* : $ty := by $body)
    logInfo m!"Final declaration:\n{stx}"
    elabDeclaration stx
  | _ => throwUnsupportedSyntax

/-
--@[progress_pure checked_add x y]
uscalar_theorem %S.checked_add_bv_spec' (x y : %S) :
  match %S.checked_add x y with
  | some z => x.val + y.val ≤ %S.max ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => %S.max < x.val + y.val
  := by
  have := core.num.checked_add_UScalar_bv_spec x y
  simp_all [U8.checked_add, UScalar.max, U8.bv]
  cases h: core.num.checked_add_UScalar x y <;> simp_all [U8.max, U8.numBits] -- TODO: remove U8
-/
--«%S»

def elabSpecialName (ty : String) (n : Name) : CommandElabM Name := do
  logInfo m!"elabSpecialName: {n}"
  match n with
  | .anonymous => pure .anonymous
  | .str pre str =>
    logInfo m!"elabSpecialName: str case: {str}"
    let str := if str == "%S" then ty else str
    pure (.str (← elabSpecialName ty pre) str)
  | .num pre i => pure (.num (← elabSpecialName ty pre) i)

partial def elabSpecial (ty : String) (stx : Syntax) : CommandElabM Syntax := do
  match stx with
  | .missing => pure .missing
  | .node info kind args =>
    let args ← args.mapM (elabSpecial ty)
    pure (.node info kind args)
  | .atom info val => pure (.atom info val)
  | .ident info rawVal val preresolved =>
    let val ← elabSpecialName ty val
    pure (.ident info rawVal val preresolved)

syntax (name := uscalarCommand) "uscalar" command : command

@[command_elab uscalarCommand]
def uscalarCommandImpl : CommandElab := fun stx => do
  logInfo ("uscalar_command (stx): " ++ stx)
  match stx with
  | `(uscalarCommand| uscalar $cmd) =>
    logInfo m!"uscalar_command: {cmd}"
    let elabOne (ty : String) := do
      let cmd ← elabSpecial ty cmd
      logInfo m!"Final declaration:\n{cmd}"
      elabDeclaration cmd
    for ty in ["U8", "U16", "U32", "U64", "U128", "Usize"] do
      elabOne ty
  | _ => throwUnsupportedSyntax


--syntax (name := uscalarThm) "uscalar_theorem'"  : command

def C : U8 := ⟨ 0, by simp ⟩

#uscalar_def1 test_def1 (%S.max) (32 : Nat)
#print test_def1

#uscalar_def1 test_def2 (C) (32 : Nat)
#print test_def2

#uscalar_def1 test_def3 (%S.max + %S.max) (32 : Nat)
#print test_def3

#uscalar_def1 test_def4 (
  match some C with
  | some z => z.val ≤ 3
  | none => false) (32 : Nat)
#print test_def4

#check U8.max

def test_def' :=
  let S := U8
  fun (x y : S) (z : ℕ) (h : x.val < 32) => (by scalar_tac : x.val + y.val < 300)

#check test_def'

uscalar_def %S.test1 (x y : %S) : Result %S := x + y

#print U8.test1

/-

uscalar @[progress_pure «%S».checked_add x y] theorem «%S».checked_add_bv_spec'' (x y : «%S») :
  match «%S».checked_add x y with
  | some z => x.val + y.val ≤ «%S».max ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => «%S».max < x.val + y.val := by
  have := core.num.checked_add_UScalar_bv_spec x y
  simp_all [«%S».checked_add, UScalar.max, «%S».bv]
  cases h: core.num.checked_add_UScalar x y <;> simp_all [«%S».max, «%S».numBits]

#check U8.checked_add_bv_spec''
#check U16.checked_add_bv_spec''


-/

end Aeneas.Std.ElabScalar
