import Lake
open Lake DSL

require aeneas from "../../backends/lean"

package «tests» {}

@[default_target] lean_lib AdtBorrows
@[default_target] lean_lib Arrays
@[default_target] lean_lib ArraysDefs
@[default_target] lean_lib ArraySliceIndex
@[default_target] lean_lib AsMut
@[default_target] lean_lib Avl
@[default_target] lean_lib BaseTutorial
@[default_target] lean_lib Bitwise
@[default_target] lean_lib BlanketImpl
@[default_target] lean_lib Builtin
@[default_target] lean_lib Constants
@[default_target] lean_lib Default
@[default_target] lean_lib DefaultedMethod
@[default_target] lean_lib Demo
@[default_target] lean_lib Deref
@[default_target] lean_lib DynamicSize
@[default_target] lean_lib Hashmap
@[default_target] lean_lib Issue194RecursiveStructProjector
@[default_target] lean_lib Issue270LoopList
@[default_target] lean_lib Issue440TypeError
@[default_target] lean_lib Joins
@[default_target] lean_lib Loops
@[default_target] lean_lib LoopsAdts
@[default_target] lean_lib LoopsIssues
@[default_target] lean_lib LoopsNested
@[default_target] lean_lib LoopsSequences
@[default_target] lean_lib MiniTree
@[default_target] lean_lib NestedBorrows
@[default_target] lean_lib NoNestedBorrows
@[default_target] lean_lib Options
@[default_target] lean_lib Order
@[default_target] lean_lib Paper
@[default_target] lean_lib PoloniusList
@[default_target] lean_lib Range
@[default_target] lean_lib RenameAttribute
@[default_target] lean_lib Scalars
@[default_target] lean_lib Slices
@[default_target] lean_lib SwitchTest
@[default_target] lean_lib Traits
@[default_target] lean_lib Tutorial
@[default_target] lean_lib Vec
