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
  | I32
  | U32

open scalar_ty

def scalar_min (ty:scalar_ty) : Int :=
  match ty with
  | I32 => i32_min
  | U32 => u32_min

def scalar_max (ty:scalar_ty) : Int :=
  match ty with
  | I32 => i32_max
  | U32 => u32_max

@[simp]
def fits (ty:scalar_ty) (x:Int) :=
  scalar_min ty <= x && scalar_max ty >= x

def scalar (ty:scalar_ty) : Type := { x : Int // fits ty x }

instance : Coe (scalar ty) Int where
  coe x := x.val

instance (n:Nat) (p : fits ty n) : OfNat (scalar ty) n where
  ofNat := ⟨ Int.ofNat n, p ⟩ 

def mk_scalar (ty: scalar_ty) (x: Int) : result (scalar ty) :=
  if h : fits ty x then ret ⟨ x, by apply h ⟩ else fail

def scalar_add (x : scalar ty) (y : scalar ty) : result (scalar ty) :=
  mk_scalar ty (Int.add x y)

/-- Some tests -/

def choose_fwd (b:Bool) (x : t) (y : t) : result t :=
  if b then ret x else ret y

def choose_bck (b:Bool) (x : t) (y : t) (z : t) : result (t × t) :=
  if b then ret (z, y) else ret (x, z)

def choose_test : result Unit := do
  let _x ← choose_fwd true 0 0
  ret ()

#eval choose_fwd true 4 3
#eval choose_fwd false 4 3