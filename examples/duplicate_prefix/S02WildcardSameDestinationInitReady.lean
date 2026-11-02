import duplicate_prefix.S02WildcardSourceGeometry
import duplicate_prefix.S02WildcardSameDestinationInitInput
import duplicate_prefix.S02WildcardSeparateDestinationReady
namespace DuplicatePrefix.S02WildcardSameDestinationInitReady
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
/-- The actual wildcard argument supplies a protected hidden source root and
all remaining return-protection resources, including coherent slot reuse. -/
theorem facts
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new .wildcard (Size.ofBytes address)) len)
    (output : GeneralBorrowForestFnEntry.Output)
    (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
    (run : GeneralBorrowRawWildcardFnEntryRuntime.operation reference.entry.allocation.extra reference.tracker.global
      ({} : FrameState) reference.id reference.offset len = .ok output) :
    let global := TypedRetagGeneric.protectedGlobal reference.tracker.global fresh
    DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree global ∧
    output.child.tree.roots.toList.Nodup ∧ GeneralBorrowWildcardParentTagOrder.ParentTagOrder output.child.tree ∧
    output.child.tree.nodes.size+1 < 65536 ∧ global.nextPointerTag.value < 18446744073709551615 ∧
    output.child.tree.locations.size = reference.entry.allocation.extra.locations.size ∧
    ∃ sourceChild sourceNode, output.child.tree.indexOfTag reference.tracker.global.nextPointerTag = some sourceChild ∧
      output.child.tree.nodeAt sourceChild = some sourceNode ∧ sourceNode.tag = reference.tracker.global.nextPointerTag ∧
      sourceNode.parent = none ∧ sourceNode.children = #[] ∧ sourceNode.isExposed = false ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive output.child.tree global.protectedTags
        (some sourceChild) (some sourceChild) (some reference.tracker.global.nextPointerTag) reference.offset len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree sourceChild .Write reference.offset (reference.offset+len) ∧
      output.global = global := by
  obtain ⟨_,_,_,positive,runtime,distinct,short,nodeRoom,tagRoom⟩ :=
    S05WildcardEntryBridge.from_positive address len reference input.contract.runtime.toState input.contract.resources
  obtain ⟨created,createdRun,tagEq,globalEq,_frame,_read,_child,afterRuntime,capacity,growth,
    sourceChild,tagged,_roots,sourcePositive,sourceActive,sourceNode,sourcePresent,sourceTag,parent,leaf,hidden⟩ :=
    GeneralBorrowRawWildcardFnEntryResources.invoke reference.entry.allocation.extra reference.tracker.global
      ({} : FrameState) reference.id runtime reference.offset len positive distinct short nodeRoom tagRoom
  have outputEq : created = output := Except.ok.inj (createdRun.symm.trans run)
  subst created
  have globalSame : output.global = TypedRetagGeneric.protectedGlobal reference.tracker.global fresh := by rw [globalEq];rfl
  rw [tagEq] at sourcePositive sourceTag tagged
  rw [globalSame] at sourcePositive afterRuntime
  obtain ⟨roots,order,_short⟩ := S02WildcardSourceGeometry.ready address len input reference output run
  have member : (reference.id,reference.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
  have margin := input.contract.resources.nodeRoom (reference.id,reference.entry) member
  have trackerEq : reference.tracker = input.contract.tracker := Option.some.inj (reference.enabled.symm.trans input.contract.runtime.enabled)
  have tags : reference.tracker.global.nextPointerTag.value.toNat+16 < 2^64 := by rw [trackerEq];exact input.contract.resources.tagRoom
  have successor := GenericFunctionEntryNumerics.successor_value reference.tracker.global.nextPointerTag fresh
  refine ⟨afterRuntime,roots,order,?_,?_,capacity,sourceChild,sourceNode,tagged,sourcePresent,sourceTag,parent,leaf,hidden,sourcePositive,sourceActive,globalSame⟩
  · change reference.entry.allocation.extra.nodes.size+16 < 65536 at margin
    omega
  · apply UInt64.lt_iff_toNat_lt.mpr
    change (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag fresh).value.toNat < 18446744073709551615
    omega
end
end DuplicatePrefix.S02WildcardSameDestinationInitReady
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSameDestinationInitReady.facts) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard same init ready dependency {dependency}"
