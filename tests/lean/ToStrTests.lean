module
public import Aeneas.Std.String
public section

open Aeneas.Std

namespace ToStrTests

/-! String literals must not add native-computation axioms to extracted code. -/

def ascii : Str := toStr "NaN"
def empty : Str := toStr ""
def utf8 : Str := toStr "αβγ ∀ 🦀"
def computed : Str := toStr ("a" ++ "b")

/-- info: 'ToStrTests.ascii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ascii

/-- info: 'ToStrTests.empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms empty

/-- info: 'ToStrTests.utf8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms utf8

/-- info: 'ToStrTests.computed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms computed

-- Kernel reduction cannot inspect opaque definitions; retain native computation
-- for this previously supported case.
opaque opaqueValue : String := "NaN"
def nativeFallback : Str := toStr opaqueValue

-- Callers can still provide a length proof for strings that are not closed expressions.
example (s : String) (h : s.toByteArray.size ≤ U32.max) : Str := toStr s h

end ToStrTests
