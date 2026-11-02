import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionFunctionArguments
import duplicate_prefix.ScopedFrame
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionFunctionScope
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts RootFrameData EmptyRootArguments ActualReferenceContext PositiveRootArguments
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def resultMachine (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (len : UInt64) :=
  {machine with
    borrowTracker := some ⟨TypedRetagGeneric.protectedGlobal tracker.global fresh,tracker.retagMode⟩
    memory := RetagEntry.updatedMemory machine.memory id entry (GeneralBorrowPositiveWildcardPartitionArgumentCopy.finalTree entry.allocation.extra tracker len)}
theorem scope
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (tracker : MachineHooks.BorrowState)
    (base len n : UInt64) (nonzero : base ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (dead1 : (root.frame.locals[1]'(root.valid i1)).value = .dead)
    (cache1 : (root.frame.locals[1]'(root.valid i1)).layout = none)
    (dead2 : (root.frame.locals[2]'(root.valid i2)).value = .dead)
    (cache2 : (root.frame.locals[2]'(root.valid i2)).layout = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (borrowFrame : FrameState) (frameBorrow : root.frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (position : Nat) (positionValid : position < machine.user.addresses.intToPtrMap.size)
    (ordered : WildcardInteriorHitAddress.Ordered machine.user.addresses.intToPtrMap)
    (addressRow : machine.user.addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (exposedAlloc : machine.user.addresses.exposed.contains id = true)
    (head : UniIndex) (headNode : TreeNode) (extras : List UniIndex)
    (nodes : UniIndex → TreeNode)
    (roots : entry.allocation.extra.roots = (head::extras).toArray)
    (headPresent : entry.allocation.extra.nodes.get head = some headNode) (headLeaf : headNode.children = #[])
    (headExposed : headNode.isExposed = true)
    (short : entry.allocation.extra.nodes.size < 65536)
    (other : ∀ root ∈ extras, entry.allocation.extra.nodes.get root = some (nodes root) ∧
      (nodes root).children = #[] ∧ (nodes root).isExposed = true)
    (well : entry.allocation.extra.locations.WellFormed)
    (treeBounds : len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (sourceAt : GeneralRangeMapState.Every
      (GeneralBorrowExposedWildcardPartitionRead.At entry.allocation.extra
        (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags head extras nodes) entry.allocation.extra.locations)
    (tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tracker.global.nextPointerTag)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (race : machine.dataRace = none)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false) :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new .wildcard (Size.ofBytes (base))) len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base))) len ActualReferenceMetadata.reference).imm
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
        ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second n)) (Storage.withCurrent frames root.frame machine) =
      .ok (2,2) (Storage.withCurrent frames (RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted borrowFrame id tracker.global.nextPointerTag) n).frame
        (resultMachine machine tracker fresh id entry len)) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new .wildcard (Size.ofBytes (base))) len ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base))) len ActualReferenceMetadata.reference).imm
  let entered := ScopedFrame.entered machine tracker .FnEntry
  let nextMachine := GeneralBorrowPositiveWildcardPartitionFunctionArguments.resultMachine entered ⟨tracker.global,.FnEntry⟩ fresh id entry len
  let nextTracker : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal tracker.global fresh,.FnEntry⟩
  have body := GeneralBorrowPositiveWildcardPartitionFunctionArguments.body options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id tracker.global base len n nonzero entry positive signedFits bounds frames root entered dead1 cache1 dead2 cache2
    ghost shallow cachedAddress present borrowFrame frameBorrow rfl fresh
    position positionValid ordered addressRow addressMode exposedAlloc head headNode extras nodes roots
    headPresent headLeaf headExposed short other well treeBounds sourceAt tagFresh noFree fits race metadata notConstructed
  have result := ScopedFrame.changed_state
    (RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second n))
    (Storage.withCurrent frames root.frame machine)
    (Storage.withCurrent frames (RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted borrowFrame id tracker.global.nextPointerTag) n).frame nextMachine)
    tracker nextTracker .FnEntry (2,2) enabled rfl body
  exact result
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionFunctionScope
