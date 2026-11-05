import RawMemoryViews.Pointer
import RawMemoryViews.ByteView
import RawMemoryViews.Initialization
import RawMemoryViews.Provenance
import RawMemoryViews.NestedBox
import RawMemoryViews.Execution
import RawMemoryViews.Ownership

/-- info: 'raw_memory_views.copy_after_deallocation.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_memory_views.copy_after_deallocation.spec

/-- info: 'raw_memory_views.ownership.dispose.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_memory_views.ownership.dispose.spec

/-- info: 'raw_memory_views.ownership.drop_owned_byte.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_memory_views.ownership.drop_owned_byte.spec

/-- info: 'Aeneas.Std.HeapWP.Runs.post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aeneas.Std.HeapWP.Runs.post

/-- info: 'raw_memory_views.usizeRepr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_memory_views.usizeRepr

/-- info: 'raw_memory_views.stored_pointer_address.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_memory_views.stored_pointer_address.spec

/-- info: 'raw_memory_views.stored_pointer_address.use_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_memory_views.stored_pointer_address.use_spec

/-- info: 'raw_memory_views.wordsRepr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_memory_views.wordsRepr

/-- info: 'raw_memory_views.update_word_bytes_raw.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_memory_views.update_word_bytes_raw.spec

/-- info: 'raw_memory_views.update_word_bytes.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_memory_views.update_word_bytes.spec

/-- info: 'raw_memory_views.first_heap_write.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_memory_views.first_heap_write.spec

/-- info: 'raw_memory_views.copy_stored_pointer.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_memory_views.copy_stored_pointer.spec

/-- info: 'raw_memory_views.copy_and_use.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_memory_views.copy_and_use.spec

/-- info: 'raw_memory_views.copy_after_deallocation_tail.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_memory_views.copy_after_deallocation_tail.spec

/-- info: 'raw_memory_views.nested_views.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_memory_views.nested_views.spec

/-- info: 'raw_memory_views.fill_raw.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_memory_views.fill_raw.spec

/-- info: 'raw_memory_views.same_address.unissued_read_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_memory_views.same_address.unissued_read_rejected

/-- info: 'raw_memory_views.retired_pointer_read_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_memory_views.retired_pointer_read_rejected

/-- info: 'Aeneas.Std.Heap.dealloc_read_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aeneas.Std.Heap.dealloc_read_rejected

/-- info: 'raw_memory_views.first_heap_write.failure_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_memory_views.first_heap_write.failure_accepted
