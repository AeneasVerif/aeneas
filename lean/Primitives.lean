inductive result (α : Type) where
  | ret : α -> result α
  | fail : result α 
deriving Repr

open result

def bind (x: result α) (f: α -> result β) : result β :=
  match x with
  | ret v  => f v 
  | fail => fail 

instance : Bind result where
  bind := bind

def massert (b:Bool) : result Unit :=
  if b then ret () else fail

def isize_min : Int := -9223372036854775808
def isize_max : Int := 9223372036854775807
def i8_min : Int := -128
def i8_max : Int := 127
def i16_min : Int := -32768
def i16_max : Int := 32767
def i32_min : Int := -2147483648
def i32_max : Int := 2147483647
def i64_min : Int := -9223372036854775808
def i64_max : Int := 9223372036854775807
def i128_min : Int := -170141183460469231731687303715884105728
def i128_max : Int := 170141183460469231731687303715884105727
def usize_min : Int := 0
def usize_max : Int := 4294967295 -- being conservative here: [u32_max] instead of [u64_max]
def u8_min : Int := 0
def u8_max : Int := 255
def u16_min : Int := 0
def u16_max : Int := 65535
def u32_min : Int := 0
def u32_max : Int := 4294967295
def u64_min : Int := 0
def u64_max : Int := 18446744073709551615
def u128_min : Int := 0
def u128_max : Int := 340282366920938463463374607431768211455

inductive scalar_ty where
  | Isize
  | I8
  | I16
  | I32
  | I64
  | I128
  | Usize
  | U8
  | U16
  | U32
  | U64
  | U128

open scalar_ty

def scalar_min (ty:scalar_ty) : Int :=
  match ty with
  | Isize => isize_min
  | I8 => i8_min
  | I16 => i16_min
  | I32 => i32_min
  | I64 => i64_min
  | I128 => i128_min
  | Usize => usize_min
  | U8 => u8_min
  | U16 => u16_min
  | U32 => u32_min
  | U64 => u64_min
  | U128 => u128_min

def scalar_max (ty:scalar_ty) : Int :=
  match ty with
  | Isize => isize_max
  | I8 => i8_max
  | I16 => i16_max
  | I32 => i32_max
  | I64 => i64_max
  | I128 => i128_max
  | Usize => usize_max
  | U8 => u8_max
  | U16 => u16_max
  | U32 => u32_max
  | U64 => u64_max
  | U128 => u128_max

abbrev fits (ty:scalar_ty) (x:Int) :=
  scalar_min ty <= x && scalar_max ty >= x

def scalar (ty:scalar_ty) : Type := { x : Int // fits ty x }

/-- An automatic coercion from scalars to Int -/
instance : Coe (scalar ty) Int where
  coe x := x.val

/-- Boolean equality for scalars, allowing us to write
    `if x = y then ...` when `x` and `y` are scalars -/
instance : BEq (scalar ty) where
  beq x y := x.val == y.val

/-- In theory, the default argument := by simp should allow Lean to automatically
    synthesizing this argument during typeclass instance synthesis.
    However, according to Henrik Boving on Zulip, default arguments in typeclass
    synthesis are currently not supported by Lean 4, which requires us
    to explicitly build scalars using the ⟨ n, by simp ⟩ notation  -/
instance (n:Nat) (p : fits ty n := by simp) : OfNat (scalar ty) n where
  ofNat := ⟨ Int.ofNat n, p ⟩ 

def mk_scalar (ty: scalar_ty) (x: Int) : result (scalar ty) :=
  /- The notation `if h : fits ty x` is Lean's sugar for a
      dependent if/then/else, allowing us to use the fact
      `fits ty x` in the then branch -/
  if h : fits ty x then ret ⟨ x, by apply h ⟩ else fail

def scalar_neg (x: scalar ty) : result (scalar ty) :=
  mk_scalar ty (-x)

def scalar_div (x y : scalar ty) : result (scalar ty) :=
  if y.val ≠ 0 then mk_scalar ty (x / y) else fail

/-- When calling this function, we try to automatically prove
    `y ≠ 0` using Lean's simplifier -/
def int_rem (x : Int) (y : Int) (_ : y ≠ 0 := by simp): Int :=
  /- Note, Lean defines a % 0 as a, but we statically
  rule out this case to match Rust semantics -/
  x % y

#eval int_rem 1 2 = 1
#eval int_rem (-1) 2 = -1
#eval int_rem 1 (-2) = 1
#eval int_rem (-1) (-2) = -1

def scalar_rem (x y : scalar ty) : result (scalar ty) :=
  if h : y.val ≠ 0 then mk_scalar ty (int_rem x y h) else fail

def scalar_add (x y : scalar ty) : result (scalar ty) :=
  mk_scalar ty (x + y)

def scalar_sub (x y : scalar ty) : result (scalar ty) :=
  mk_scalar ty (x - y)

def scalar_mul (x y : scalar ty) : result (scalar ty) :=
  mk_scalar ty (x * y)

/-- Cast an integer from a `src_ty` to a `tgt_ty` -/
def scalar_cast (tgt_ty : scalar_ty) (x : scalar src_ty)
  : result (scalar tgt_ty) :=
  mk_scalar tgt_ty x



/-- Some tests -/

def choose_fwd (b:Bool) (x y : t) : result t :=
  if b then ret x else ret y

def choose_bck (b:Bool) (x y z : t) : result (t × t) :=
  if b then ret (z, y) else ret (x, z)

def choose_test : result Unit := do
  let i : scalar I32 ← choose_fwd true ⟨ 0, by simp ⟩ ⟨ 0, by simp ⟩ 
  let z ← scalar_add i ⟨ 1, by simp ⟩
  massert (z == ⟨ 1, by simp ⟩ )
  let ⟨ x0, y0 ⟩ ← choose_bck true ⟨ 0, by simp ⟩ ⟨ 0, by simp ⟩ z
  massert (x0 == ⟨ 1, by simp ⟩ )
  massert (y0 == ⟨ 0, by simp ⟩ ) 
  ret ()

#eval choose_test

#eval choose_fwd true 4 3
#eval choose_fwd false 4 3
