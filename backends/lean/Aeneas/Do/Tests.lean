import Aeneas.Do.Elab
import Aeneas.Do.Delab
import Aeneas.Std

namespace Do
namespace Tests

open Aeneas Std Result ControlFlow Error

def test1 : Result Nat := do
  ok 42
/--
info: def test1 : Result ℕ :=
ok 42
-/
#guard_msgs in
#print test1

def test2 : Result Nat := do
  let x ← ok 1
  ok x
/--
info: def test2 : Result ℕ :=
do
  let x ← ok 1
  ok x
-/
#guard_msgs in
#print test2

def test3 : Result Nat := do
  let x ← ok 1
  let y ← ok 2
  ok (x + y)
/--
info: def test3 : Result ℕ :=
do
  let x ← ok 1
  let y ← ok 2
  ok (x + y)
-/
#guard_msgs in
#print test3

def test4 : Result Nat := do
  let x : Nat ← ok 1
  ok (x + 1)
/--
info: def test4 : Result ℕ :=
do
  let x ← ok 1
  ok (x + 1)
-/
#guard_msgs in
#print test4

def test5 : Result Nat := do
  let x := 1
  ok (x + 2)
/--
info: def test5 : Result ℕ :=
have x := 1;
ok (x + 2)
-/
#guard_msgs in
#print test5

def test6 : Result Nat := do
  let x : Nat := 1
  let y ← ok 2
  ok (x + y)
/--
info: def test6 : Result ℕ :=
have x := 1;
do
let y ← ok 2
ok (x + y)
-/
#guard_msgs in
#print test6

def test7 : Result Nat := do
  let x ← ok 1
  if x > 0 then ok x else ok 0
/--
info: def test7 : Result ℕ :=
do
  let x ← ok 1
  if x > 0 then ok x else ok 0
-/
#guard_msgs in
#print test7

def test8 : Result Nat := do
  let x ← ok 1
  if x > 0 then ok 10 else ok 20
/--
info: def test8 : Result ℕ :=
do
  let x ← ok 1
  if x > 0 then ok 10 else ok 20
-/
#guard_msgs in
#print test8

def test9 : Result Nat := do
  let x ← ok 2
  let y ← do
    if x > 1 then ok 1 else ok 0
  ok y
/--
info: def test9 : Result ℕ :=
do
  let x ← ok 2
  let y ← if x > 1 then ok 1 else ok 0
  ok y
-/
#guard_msgs in
#print test9

def test10 : Result Nat := do
  let x ← ok 2
  let y ← if x > 1 then ok 1 else ok 0
  ok y
/--
info: def test10 : Result ℕ :=
do
  let x ← ok 2
  let y ← if x > 1 then ok 1 else ok 0
  ok y
-/
#guard_msgs in
#print test10

def test11_body (max i : Nat) : Result (ControlFlow Nat Nat) :=
  if i < max then ok (ControlFlow.cont (i + 1))
  else ok (ControlFlow.done i)

def test11 : Result Nat := do
  let max ← ok 10
  loop (test11_body max) 0
/--
info: def test11 : Result ℕ :=
do
  let max ← ok 10
  loop (test11_body max) 0
-/
#guard_msgs in
#print test11

def test12 : Result Nat := do
  let (a, b) ← ok (1, 2)
  ok (a + b)
/--
info: def test12 : Result ℕ :=
do
  let (a, b) ← ok (1, 2)
  ok (a + b)
-/
#guard_msgs in
#print test12

def test13 : Result Nat := do
  let (_, b) ← ok (1, 2)
  ok b
/--
info: def test13 : Result ℕ :=
do
  let (_, b) ← ok (1, 2)
  ok b
-/
#guard_msgs in
#print test13

def test14 : Result Nat := do
  let (a, b) := (1, 2)
  ok (a + b)
/--
info: def test14 : Result ℕ :=
let (a, b) := (1, 2)
ok (a + b)
-/
#guard_msgs in
#print test14

def test15 : Result Nat := do
  let x ← ok 1
  match x with
  | 0 => ok 10
  | _ => ok 20
/--
info: def test15 : Result ℕ :=
do
  let x ← ok 1
  match x with
    | 0 => ok 10
    | x => ok 20
-/
#guard_msgs in
#print test15

def test16 : Result Nat := do
  let x ← ok 1
  let y ← match x with
    | 0 => ok 10
    | _ => ok 20
  ok (y + 1)
/--
info: def test16 : Result ℕ :=
do
  let x ← ok 1
  let y ←
    match x with
      | 0 => ok 10
      | x => ok 20
  ok (y + 1)
-/
#guard_msgs in
#print test16

def massert_test : Result Unit := do
  let s ←
    lift (Array.to_slice
      (Array.make 5#usize [ 0#u32, 1#u32, 2#u32, 3#u32, 4#u32 ]))
  let i ← core.slice.Slice.iter s
  let it ← core.slice.iter.IteratorSliceIter.step_by i 1#usize
  let (o, it1) ←
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U32) it
  let i1 ← core.option.Option.unwrap o
  massert (i1 = 0#u32)
  let (o1, it2) ←
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U32) it1
  let i2 ← core.option.Option.unwrap o1
  massert (i2 = 1#u32)
/--
info: def massert_test : Result Unit :=
do
  let s ← lift (Array.make 5#usize [0#u32, 1#u32, 2#u32, 3#u32, 4#u32] massert_test._proof_7).to_slice
  let i ← core.slice.Slice.iter s
  let it ← core.slice.iter.IteratorSliceIter.step_by i 1#usize
  let (o, it1) ← core.iter.adapters.step_by.IteratorStepBy.next (core.iter.traits.iterator.IteratorSliceIter U32) it
  let i1 ← core.option.Option.unwrap o
  massert (i1 = 0#u32)
  let (o1, it2) ← core.iter.adapters.step_by.IteratorStepBy.next (core.iter.traits.iterator.IteratorSliceIter U32) it1
  let i2 ← core.option.Option.unwrap o1
  massert (i2 = 1#u32)
-/
#guard_msgs in
#print massert_test

def bool_test (x : Bool) : Result Bool := do
  let b ← ok x
  if b
  then ok true
  else ok false
/--
info: def bool_test : Bool → Result Bool :=
fun x => do
  let b ← ok x
  if b = true then ok true else ok false
-/
#guard_msgs in
#print bool_test

opaque core.mem.drop {T : Type} : T → Result Unit

def do_nested_test (b1 : Bool) : Result Unit := do
  let _ ←
    if b1
    then ok (true, 2#u32)
    else ok (false, 0#u32)
  ok ()
/--
info: def do_nested_test : Bool → Result Unit :=
fun b1 => do
  let _ ← if b1 = true then ok (true, 2#u32) else ok (false, 0#u32)
  ok ()
-/
#guard_msgs in
#print do_nested_test

def if_then_add_test (b : Bool) (x : Std.U32) : Result Std.U32 := do
  let y ← if b then ok 1#u32 else ok 0#u32
  x + y
/--
info: def if_then_add_test : Bool → U32 → Result U32 :=
fun b x => do
  let y ← if b = true then ok 1#u32 else ok 0#u32
  x + y
-/
#guard_msgs in
#print if_then_add_test

def match_add_test (a : Std.U32) (x : Std.U32) : Result Std.U32 := do
  let y ←
    match a with
    | 0#uscalar => ok 0#u32
    | 1#uscalar => ok 1#u32
    | _ => ok 2#u32
  x + y
/--
info: def match_add_test : U32 → U32 → Result U32 :=
fun a x => do
  let y ←
    match a with
      | 0#32#uscalar => ok 0#u32
      | 1#32#uscalar => ok 1#u32
      | x => ok 2#u32
  x + y
-/
#guard_msgs in
#print match_add_test

def make2nats (x y : Nat) : Result (Nat × Nat) := do
  ok (x, y)

def make3nats (x y z : Nat) : Result ((Nat × Nat) × Nat) := do
  ok ((x, y), z)

def make4nats (x y z w : Nat) : Result ((Nat × Nat) × (Nat × Nat)) := do
  ok ((x, y), z, w)

def nested_pat_test : Result Nat := do
  let (a, b) ← make2nats 1 2
  let ((c, d), e) ← make3nats 3 4 5
  let ((f, g), (h, i)) ← make4nats 6 7 8 9
  ok (a + b + c + d + e + f + g + h + i)
/--
info: def nested_pat_test : Result ℕ :=
do
  let (a, b) ← make2nats 1 2
  let ((c, d), e) ← make3nats 3 4 5
  let ((f, g), (h, i)) ← make4nats 6 7 8 9
  ok (a + b + c + d + e + f + g + h + i)
-/
#guard_msgs in
#print nested_pat_test

structure TwoNatsWrapped where
  x : Nat
  y : Nat

structure FourNatsWrapped where
  z : TwoNatsWrapped
  w : TwoNatsWrapped

def make2natswrapped (x y : Nat) : Result TwoNatsWrapped := do
  ok { x, y }

def make4natswrapped (w₁ w₂ : TwoNatsWrapped) : Result FourNatsWrapped := do
  ok ⟨w₁, w₂⟩

def nested_wrapped_pat_test : Result Nat := do
  let w₁ ← make2natswrapped 1 2
  let w₂ ← make2natswrapped 3 4
  let ⟨⟨x, y⟩, ⟨z, w⟩⟩ ← make4natswrapped w₁ w₂
  ok (x + y + z + w)
/--
info: def nested_wrapped_pat_test : Result ℕ :=
do
  let w₁ ← make2natswrapped 1 2
  let w₂ ← make2natswrapped 3 4
  let ⟨⟨x, y⟩, ⟨z, w⟩⟩ ← make4natswrapped w₁ w₂
  ok (x + y + z + w)
-/
#guard_msgs in
#print nested_wrapped_pat_test

def big_pat_test : Result Nat := do
  let (x, y, z, w) := (1,2,3,4)
  let (a, b, c, d) ← ok (5, 6, 7, 8)
  ok (x + y + z + w + a + b + c + d)
/--
info: def big_pat_test : Result ℕ :=
let (x, y, z, w) := (1, 2, 3, 4)
do
let (a, b, c, d) ← ok (5, 6, 7, 8)
ok (x + y + z + w + a + b + c + d)
-/
#guard_msgs in
#print big_pat_test

structure Wrapper (T : Type) where
  x : T

def make_wrapper {T : Type} (x : T) :
  Result ((Wrapper T) × (Wrapper T → Wrapper T)) := do
  ok ({ x }, fun w => w)

def universe_test {T : Type} (w : Wrapper T) :
  Result ((Wrapper T) × (Wrapper T → Wrapper T)) := do
  let (inner, back) ← make_wrapper w.x
  let back2 := fun w1 => back { w with x := w1.x }
  ok (inner, back2)
/--
info: def universe_test : {T : Type} → Wrapper T → Result (Wrapper T × (Wrapper T → Wrapper T)) :=
fun {T} w => do
  let (inner, back) ← make_wrapper w.x
  have back2 : Wrapper T → Wrapper T := fun w1 => back { x := w1.x }
  ok (inner, back2)
-/
#guard_msgs in
#print universe_test

def make_pair {T : Type} (x y : T) :
  Result (T × T × (T → List T) × (T → List T)) := do
  ok (x, y, fun t => [t], fun t => [t])

def universe_tuple_test {T : Type} (x y : T) :
  Result ((T × T) × ((T × T) → (List T × List T))) := do
  let (a, b, back, back1) ← make_pair x y
  let back2 :=
    fun p =>
      let (t1, t2) := p
      (back t1, back1 t2)
  ok ((a, b), back2)
/--
info: def universe_tuple_test : {T : Type} → T → T → Result ((T × T) × (T × T → List T × List T)) :=
fun {T} x y => do
  let (a, b, back, back1) ← make_pair x y
  have back2 : T × T → List T × List T := fun p =>
    match p with
    | (t1, t2) => (back t1, back1 t2)
  ok ((a, b), back2)
-/
#guard_msgs in
#print universe_tuple_test

def get_and_update (xs : alloc.vec.Vec U32) (i : Usize) :
  Result (U32 × (U32 → alloc.vec.Vec U32)) := do
  let x ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) xs i
  ok (x, fun _v => xs)

def mono_loop_test (xs : alloc.vec.Vec U32) (i : Usize) :
  Result (alloc.vec.Vec U32) := do
  let i1 := alloc.vec.Vec.len xs
  if i < i1
  then
    let (_, update_back) ← get_and_update xs i
    let i2 ← i + 1#usize
    let xs1 := update_back 0#u32
    mono_loop_test xs1 i2
  else ok xs
partial_fixpoint
/--
info: @[irreducible] def mono_loop_test : alloc.vec.Vec U32 → Usize → Result (alloc.vec.Vec U32) :=
Lean.Order.fix
  (fun f xs i =>
    let i1 := xs.len;
    if i < i1 then do
      let (_, update_back) ← get_and_update xs i
      let i2 ← i + 1#usize
      let xs1 : alloc.vec.Vec U32 := update_back 0#u32
      f xs1 i2
    else ok xs)
  mono_loop_test._proof_1
-/
#guard_msgs in
#print mono_loop_test

def doIf_pat_test (b : Bool) : Result (Nat × Nat) := do
  let (x, y) ←
    if b then ok (1, 2) else ok (3, 4)
  ok (x, y)
/--
info: def doIf_pat_test : Bool → Result (ℕ × ℕ) :=
fun b => do
  let (x, y) ← if b = true then ok (1, 2) else ok (3, 4)
  ok (x, y)
-/
#guard_msgs in
#print doIf_pat_test

def match_pat_test (n : Nat) : Result (Nat × Nat) := do
  let (x, y) ←
    match n with
    | 0 => ok (1, 2)
    | _ => ok (3, 4)
  ok (x, y)
/--
info: def match_pat_test : ℕ → Result (ℕ × ℕ) :=
fun n => do
  let (x, y) ←
    match n with
      | 0 => ok (1, 2)
      | x => ok (3, 4)
  ok (x, y)
-/
#guard_msgs in
#print match_pat_test

def else_if_test (x y : Nat) : Result Ordering := do
  if x < y
  then ok Ordering.lt
  else if x = y
  then ok Ordering.eq
  else ok Ordering.gt
/--
info: def else_if_test : ℕ → ℕ → Result Ordering :=
fun x y => if x < y then ok Ordering.lt else if x = y then ok Ordering.eq else ok Ordering.gt
-/
#guard_msgs in
#print else_if_test

inductive Wrap where
  | mk : Nat → Wrap

def anon_ctor_test (w : Wrap) : Result Nat := do
  let ⟨ n ⟩ := w
  ok (n + 1)
/--
info: def anon_ctor_test : Wrap → Result ℕ :=
fun w =>
  let ⟨n⟩ := w
  ok (n + 1)
-/
#guard_msgs in
#print anon_ctor_test

def anon_ctor_monadic_test (w : Wrap) : Result Nat := do
  let ⟨ n ⟩ ← ok w
  ok (n + 1)
/--
info: def anon_ctor_monadic_test : Wrap → Result ℕ :=
fun w => do
  let ⟨n⟩ ← ok w
  ok (n + 1)
-/
#guard_msgs in
#print anon_ctor_monadic_test

structure ExBox (Inst : Type → Type) where
  ty : Type
  inst : Inst ty
  val : ty

structure Into2 (Self : Type) (T : Type) where
  into : Self → Result T

def exbox_lambda_test {V T W : Type}
    (inst1 : Into2 T V) (inst2 : Into2 W V)
    (b : Bool) (x : T) (y : W) :
    Result (ExBox (fun _dyn => Into2 _dyn V)) := do
  if b
  then ok (ExBox.mk _ inst1 x)
  else ok (ExBox.mk _ inst2 y)
/--
info: def exbox_lambda_test : {V T W : Type} →
  Into2 T V → Into2 W V → Bool → T → W → Result (ExBox fun _dyn => Into2 _dyn V) :=
fun {V T W} inst1 inst2 b x y =>
  if b = true then ok { ty := T, inst := inst1, val := x } else ok { ty := W, inst := inst2, val := y }
-/
#guard_msgs in
#print exbox_lambda_test

def do_if_rest_test : Result Nat := do
  let b ← ok true
  if b then ok () else ok ()
  if b then ok () else ok ()
  if b then ok () else ok ()
  ok 1
/--
info: def do_if_rest_test : Result ℕ :=
do
  let b ← ok true
  if b = true then ok () else ok ()
  if b = true then ok () else ok ()
  if b = true then ok () else ok ()
  ok 1
-/
#guard_msgs in
#print do_if_rest_test

inductive MatchTest | A | B | C

def do_match_rest_test (m : MatchTest) : Result Nat := do
  let n ← ok 3
  match m with
  | .A => ok ()
  | .B => ok ()
  | .C => ok ()
  match m with
  | .A => ok ()
  | .B => ok ()
  | .C => ok ()
  pure n
/--
info: def do_match_rest_test : MatchTest → Result ℕ :=
fun m => do
  let n ← ok 3
  match m with
    | MatchTest.A => ok ()
    | MatchTest.B => ok ()
    | MatchTest.C => ok ()
  match m with
    | MatchTest.A => ok ()
    | MatchTest.B => ok ()
    | MatchTest.C => ok ()
  pure n
-/
#guard_msgs in
#print do_match_rest_test

end Tests
end Do
