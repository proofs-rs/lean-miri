import Miri.Verification.ExactWP

namespace MiriTests.Verification.TreeEffectsWP

open Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Verification.TreeEffectsWP Std.WP

set_option experimental.vcgen true

variable {K U : Type} [DecidableEq K]

/-- Production exposure runs the selected tree's ordered mutation and reports
its exact memory commit or failure to the client. -/
example (id : AllocId) (allocation : Allocation Provenance BorrowTree)
    (tags : ProtectedTags) (tag : BorTag) (post : Unit → PointerMachine.State K U → Prop)
    (failure : StepError → PointerMachine.State K U → Prop) :
    Triple (PointerMachine.exposeTree id allocation tags tag)
      (exposeTreePre id allocation tags tag post failure) post failure := by
  vcgen <;> assumption

/-- Each production GC iteration discharges the selected tree's pruning
precondition before advancing to the next allocation. -/
example (id : AllocId) (allocation : Allocation Provenance BorrowTree) (live : Array BorTag)
    (post : Unit → MachineHooks.State K U → Prop) (failure : StepError → MachineHooks.State K U → Prop) :
    Triple (ProvenanceGC.collectTree id allocation live)
      (collectTreePre id allocation live post failure) post failure := by
  vcgen <;> assumption

end MiriTests.Verification.TreeEffectsWP
