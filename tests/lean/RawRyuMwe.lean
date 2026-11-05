module

public import RawRyuMwe.Memory
public import RawRyuMwe.ByteOps
public import RawRyuMwe.Outputs
public import RawRyuMwe.Readback
public import RawRyuMwe.Buffers
public import RawRyuMwe.SafeOutputs
public import RawRyuMwe.TableCopy

/- These are handwritten heap-model MWEs, not successful compiler emissions.
   The Rust extraction failures are recorded alongside their source files. -/

/-- info: 'scalar_mwe.u64Repr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scalar_mwe.u64Repr

/-- info: 'scalar_mwe.u16Repr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scalar_mwe.u16Repr

/-- info: 'raw_ryu_mwe.initialized_outputs.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_ryu_mwe.initialized_outputs.spec

/-- info: 'raw_ryu_mwe.initialized_outputs_scoped.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_ryu_mwe.initialized_outputs_scoped.spec

/-- info: 'raw_ryu_mwe.buffer_as.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_ryu_mwe.buffer_as.spec

/-- info: 'raw_ryu_mwe.buffer_cast.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_ryu_mwe.buffer_cast.spec

/-- info: 'raw_ryu_mwe.copy_table.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_ryu_mwe.copy_table.spec
