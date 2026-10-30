module

public import RawDoublyLinked.Types
public import Aeneas.Std.Heap.EffectSpecs

@[expose] public section

open Aeneas.Std

namespace raw_doubly_linked.ext

/- The descriptor is an explicit model parameter, including the representations
of stored pointers. No Rust node-layout or pointer-encoding axiom is assumed. -/
def read_node (repr : Aeneas.Std.Repr Node) (p : MutRawPtr Node) : Result Node :=
  RawPtr.read repr p

def write_node (repr : Aeneas.Std.Repr Node) (p : MutRawPtr Node) (node : Node) : Result Unit :=
  MutRawPtr.write repr p node

def blankNode (value : U32) : Node :=
  .mk ⟨0#usize, 0#usize⟩ ⟨0#usize, 0#usize⟩ value

def allocate_node (repr : Aeneas.Std.Repr Node) (value : U32) : Result (MutRawPtr Node) :=
  alloc.boxed.Box.into_raw repr (blankNode value)

def take_node (repr : Aeneas.Std.Repr Node) (p : MutRawPtr Node) : Result Node :=
  alloc.boxed.Box.from_raw repr p

end raw_doubly_linked.ext
