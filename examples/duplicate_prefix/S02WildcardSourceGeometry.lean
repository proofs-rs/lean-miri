import duplicate_prefix.S02WildcardSourceOrder
import duplicate_prefix.GeneralBorrowRawWildcardFnEntryScopedResources
import duplicate_prefix.S05WildcardEntryBridge
import duplicate_prefix.S05ConsistentCallSpecification

namespace DuplicatePrefix.S02WildcardSourceGeometry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- All release-time graph geometry of the actual wildcard FnEntry source
comes from the original contract's runtime and node margin. -/
theorem ready
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len)
    (output : GeneralBorrowForestFnEntry.Output)
    (run : GeneralBorrowRawWildcardFnEntryRuntime.operation reference.entry.allocation.extra
      reference.tracker.global ({} : FrameState) reference.id reference.offset len = .ok output) :
    output.child.tree.roots.toList.Nodup ∧
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder output.child.tree ∧
    output.child.tree.nodes.size < 65536 := by
  obtain ⟨_,_,_,capability,runtime,distinct,short,nodeRoom,tagRoom⟩ :=
    S05WildcardEntryBridge.from_positive address len reference input.contract.runtime.toState
      input.contract.resources
  obtain ⟨constructed,created,_tag,_global,_frame,_access,_child,_runtime,_capacity,growth,
    roots,_index,_lookup,_positive,_activity,_node⟩ :=
    GeneralBorrowRawWildcardFnEntryScopedResources.invoke reference.entry.allocation.extra
      reference.tracker.global {} reference.id runtime reference.offset len capability distinct short
      nodeRoom tagRoom
  have same : constructed = output := Except.ok.inj (created.symm.trans run)
  subst constructed
  have member : (reference.id,reference.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
  have originalOrder := input.contract.runtime.parentTags (reference.id,reference.entry) member
  have margin := input.contract.resources.nodeRoom (reference.id,reference.entry) member
  change reference.entry.allocation.extra.nodes.size + 16 < 65536 at margin
  have nextOrder := S02WildcardSourceOrder.ordered reference.entry.allocation.extra
    reference.tracker.global {} reference.id runtime reference.offset len capability distinct short
    nodeRoom tagRoom originalOrder output run
  exact ⟨roots,nextOrder,by omega⟩

end
end DuplicatePrefix.S02WildcardSourceGeometry

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSourceGeometry.ready) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard source-geometry dependency {dependency}"
