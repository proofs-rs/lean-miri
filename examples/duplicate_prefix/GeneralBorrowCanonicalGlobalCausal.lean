import duplicate_prefix.ActualRetagContext
import duplicate_prefix.GlobalDataOnlyActualConfig
import duplicate_prefix.RetagPointerChecks
import duplicate_prefix.GeneralBorrowParentTagRootFrames
import duplicate_prefix.GeneralBorrowEffectfulTreeUpdateFrame
import duplicate_prefix.GeneralBorrowTypedTreeUpdateCausalFrame
namespace DuplicatePrefix.GeneralBorrowCanonicalGlobalCausal
open Miri Miri.Input Miri.Memory Miri.ABI Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts GeneralBorrowEffectfulTreeUpdateFrame GeneralBorrowWildcardParentTagOrder
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
set_option diagnostics false
noncomputable section

/-- The actual canonical ensure on an already-live allocation does not call
any global conversion callback. The premise is initial lookup data, not success
of ensure, retag or the target call. -/
theorem live_noop (options : EvalConfigurationCore.Options)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualRetagContext.Context options remaining span)
    (state : RootState) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry)) :
    (ActualReferenceContext.config options remaining span).retag.ensureTreeExtra id state = .ok () state := by
  have equal := ctx.source.ensure.trans ctx.ensure
  have stored := RetagPointerChecks.ensure_tree_live .global ctx.globals ctx.synchronize state id entry present
  have linked : (ActualReferenceContext.config options remaining span).retag.ensureTreeExtra id state =
      GlobalAllocationMachine.ensure .global ctx.globals id state := congrFun (congrFun equal id) state
  exact linked.trans stored

theorem live_preserves (P : AllocId → BorrowTree → Prop) (options : EvalConfigurationCore.Options)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualRetagContext.Context options remaining span)
    (state : RootState) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (before : AllTrees P state.machine.memory) :
    GeneralBorrowTypedTreeUpdateCausalFrame.Holds P
      ((ActualReferenceContext.config options remaining span).retag.ensureTreeExtra id state) := by
  exact Eq.mpr (congrArg (GeneralBorrowTypedTreeUpdateCausalFrame.Holds P)
    (live_noop options remaining span ctx state id entry present)) before

/-- Real lazy global materialization adds a parentless root. Supported means
explicit compiler allocation/relocation metadata, not an operation-success
certificate. This theorem covers this known metadata family only; it does NOT
claim arbitrary native/extern/static hook coverage. -/
theorem lazy_supported_preserves (P : AllocId → BorrowTree → Prop)
    (seed : ∀ id tag size, P id (BorrowTree.new tag size)) (options : EvalConfigurationCore.Options) (choice : Unit)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : RootState) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (supported : GlobalSupportedImage.Supported source PreparedReflection.actual.compiler.runtime.target
      before.machine.memory tracker.global.rootPointerTags before.machine.user.addresses.baseAddr)
    (enabled : before.machine.borrowTracker = some tracker)
    (rootCached : tracker.global.rootTag? id = some root)
    (race : before.machine.dataRace = none)
    (noExtras : (before.machine.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id)) = false)
    (absent : before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (descriptor : before.machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (orders : AllTrees P before.machine.memory) :
    GeneralBorrowTypedTreeUpdateCausalFrame.Holds P
      ((PreparedContracts.actualConfig options choice remaining span).retag.ensureTreeExtra id before) := by
  obtain ⟨converted,attributes,ensured⟩ := GlobalDataOnlyActualConfig.ensure_success options choice remaining span
    before tracker id root source supported enabled rootCached race noExtras absent descriptor
  apply Eq.mpr (congrArg (GeneralBorrowTypedTreeUpdateCausalFrame.Holds P) ensured)
  intro row member
  change row ∈ ((before.machine.memory.live.filter fun old => old.1 != id).push
    (id,⟨.machine .global,converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)⟩)).toList at member
  rw [Array.toList_push] at member
  rcases List.mem_append.mp member with old | new
  · rw [Array.toList_filter] at old
    exact orders row (List.mem_filter.mp old).1
  · have equal := List.mem_singleton.mp new
    subst row
    exact seed id root source.byteSize
end
end DuplicatePrefix.GeneralBorrowCanonicalGlobalCausal
