import duplicate_prefix.GeneralBorrowRawWildcardWindowInitial
import duplicate_prefix.GeneralBorrowRawWildcardWindowFunctionInvocationResources
import duplicate_prefix.GeneralBorrowRawWildcardFunctionInvocationResources
import duplicate_prefix.GeneralBorrowRawWildcardFnEntryScopedResources
namespace DuplicatePrefix.GeneralBorrowRawWildcardWindowInitialize
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver GeneralBorrowRawWildcardWindowInitial
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

structure Packet (s : Initial) (n : UInt64) where
  output : GeneralBorrowForestFnEntry.Output
  operation : GeneralBorrowRawWildcardFnEntryRuntime.operation s.entry.allocation.extra s.tracker.global {} s.id (offset s) s.len = .ok output
  slotAllocation : Allocation Provenance BorrowTree
  slotProperties : SlotProperties s slotAllocation
  call : ActualCall s n (caller s n) (machine s output slotAllocation)
  child : UniIndex
  lookup : output.child.tree.indexOfTag s.tracker.global.nextPointerTag = some child
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree (global s).global
  positive : GeneralBorrowFreshRootScopedRow.Positive output.child.tree (global s).global.protectedTags
    child child s.tracker.global.nextPointerTag (offset s) s.len
  activity : GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write (offset s) (offset s+s.len)
  capacity : output.child.tree.locations.size = s.entry.allocation.extra.locations.size
  growth : output.child.tree.nodes.size ≤ s.entry.allocation.extra.nodes.size+1
  distinct : output.child.tree.roots.toList.Nodup
  roots : output.child.tree.roots = s.entry.allocation.extra.roots.push child
  node : TreeNode
  nodePresent : output.child.tree.nodeAt child = some node
  nodeTag : node.tag = s.tracker.global.nextPointerTag
  parentless : node.parent = none
  leaf : node.children = #[]
  hidden : node.isExposed = false
  buffer : (machine s output slotAllocation).memory.live.find? (fun row => row.1 == s.id) =
    some (s.id,{s.entry with allocation := s.entry.allocation.setExtra output.child.tree})
  slot : (machine s output slotAllocation).memory.live.find? (fun row => row.1 == s.slotId) =
    some (s.slotId,{s.slotEntry with allocation := slotAllocation})
  tracked : (machine s output slotAllocation).borrowTracker = some (global s)

private theorem initializes_raw (s : Initial) (n : UInt64) :
    ∃ output : GeneralBorrowForestFnEntry.Output,
      GeneralBorrowRawWildcardFnEntryRuntime.operation s.entry.allocation.extra s.tracker.global {} s.id (offset s) s.len = .ok output ∧
      ∃ slotAllocation : Allocation Provenance BorrowTree,
        ActualCall s n (caller s n) (machine s output slotAllocation) ∧ SlotProperties s slotAllocation := by
  rcases s.geometry with ⟨same,position,valid,ordered,row⟩ | ⟨position,cut,row,inside⟩
  · have bounds : s.len.toNat ≤ s.entry.allocation.byteSize.bytes.toNat := by
      simpa only [same,UInt64.sub_self,UInt64.toNat_zero,Nat.zero_add] using s.bounds
    have capability : DuplicatePrefixBorrowAuthorization.Positive s.entry.allocation.extra s.tracker.global.protectedTags none none none 0 s.len := by
      simpa only [same,UInt64.sub_self] using s.capability
    obtain ⟨output,run,allocation,call,properties,rest⟩ :=
      GeneralBorrowRawWildcardFunctionInvocationResources.enters s.options s.limits s.remaining s.span s.ctx s.debugOff s.cmp
        s.dynamicFuel s.validityFuel s.fuelEq s.validationEq s.id s.tracker s.base s.len n (by simpa only [same] using s.nonzero)
        s.entry s.positive s.signedFits bounds s.before s.ghost s.shallow s.cachedAddress s.present s.enabled s.fresh
        position valid ordered row s.addressMode s.exposedAlloc s.runtime capability s.distinct (by have h:=s.nodeHeadroom;omega) (by have h:=s.nodeHeadroom;omega)
        s.race s.metadata s.notConstructed s.retagCtx s.place s.layout s.slotId s.slotEntry s.slotBase s.slotRoot s.slotPointer s.aligned
        s.slotCached s.slotTree s.slotSize s.slotPresent s.separate s.slotFresh s.slotDistinct s.slotParentDistinct s.slotFree
        s.mutable s.storage s.maskLength s.provenance s.noBackend s.extras s.thread s.active s.noCache
    refine ⟨output,?_,allocation,?_,?_⟩
    · simpa only [offset,same,UInt64.sub_self] using run
    · simpa only [ActualCall,caller,machine,adjusted,same,PositiveRootInstalledFrame.installed,
        CanonicalCopy.replaceAllocation,ReturnProtection.borrowedState,Storage.withCurrent,
        GeneralBorrowRawWildcardFunctionState.enteredMachine,GeneralBorrowRawWildcardWindowFunctionState.enteredMachine,
        GeneralBorrowRawWildcardFunctionState.next,GeneralBorrowRawWildcardWindowFunctionState.next,
        GeneralBorrowRawWildcardFunctionScope.resultMachine,GeneralBorrowRawWildcardWindowFunctionScope.resultMachine,
        GeneralBorrowRawWildcardFunctionArguments.resultMachine,GeneralBorrowRawWildcardWindowFunctionArguments.resultMachine] using call
    · exact properties
  · obtain ⟨output,run,allocation,call,properties,rest⟩ :=
      GeneralBorrowRawWildcardWindowFunctionInvocationResources.enters s.options s.limits s.remaining s.span s.ctx s.debugOff s.cmp
        s.dynamicFuel s.validityFuel s.fuelEq s.validationEq s.id s.tracker s.address s.base s.len n s.nonzero
        s.entry s.positive s.signedFits s.bounds s.before s.ghost s.shallow s.cachedAddress s.present s.enabled s.fresh
        position cut inside row s.addressMode s.exposedAlloc s.runtime s.capability s.distinct (by have h:=s.nodeHeadroom;omega) (by have h:=s.nodeHeadroom;omega)
        s.race s.metadata s.notConstructed s.retagCtx s.place s.layout s.slotId s.slotEntry s.slotBase s.slotRoot s.slotPointer s.aligned
        s.slotCached s.slotTree s.slotSize s.slotPresent s.separate s.slotFresh s.slotDistinct s.slotParentDistinct s.slotFree
        s.mutable s.storage s.maskLength s.provenance s.noBackend s.extras s.thread s.active s.noCache
    exact ⟨output,run,allocation,call,properties⟩

/-- Internal description of the already-derived actual initializer endpoint.
Public initializes below derives every operational premise from Initial. -/
theorem described (s : Initial) (n : UInt64) (output : GeneralBorrowForestFnEntry.Output)
    (run : GeneralBorrowRawWildcardFnEntryRuntime.operation s.entry.allocation.extra s.tracker.global {} s.id (offset s) s.len = .ok output)
    (allocation : Allocation Provenance BorrowTree)
    (call : ActualCall s n (caller s n) (machine s output allocation))
    (properties : SlotProperties s allocation) :
    ∃ packet : Packet s n, packet.output = output ∧ packet.slotAllocation = allocation := by
  obtain ⟨resourceOutput,resourceRun,tagEq,globalEq,frameEq,readDone,childDone,rawRuntime,capacity,growth,distinct,child,lookup,roots,⟨owner⟩,activity,geometry⟩ :=
    GeneralBorrowRawWildcardFnEntryScopedResources.invoke s.entry.allocation.extra s.tracker.global {} s.id s.runtime (offset s) s.len
      s.capability s.distinct (by have h:=s.nodeHeadroom;omega) (by have h:=s.nodeHeadroom;omega) s.fresh
  have same : resourceOutput = output := Except.ok.inj (resourceRun.symm.trans run)
  subst resourceOutput
  rw [tagEq] at lookup owner
  have globals : output.global = (GeneralBorrowRawWildcardWindowFunctionState.next s.tracker s.fresh).global := globalEq
  rw [globals] at rawRuntime owner
  obtain ⟨allocated,held,pushed,finalRuntime,finalPositive,freshTag⟩ :=
    GeneralBorrowFreshRootScopedRegistration.prepare output.child.tree (GeneralBorrowRawWildcardWindowFunctionState.next s.tracker s.fresh).global
      (({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag) s.slotId s.slotFresh rawRuntime
      child child s.tracker.global.nextPointerTag (offset s) s.len owner
  obtain ⟨node,nodePresent,nodeTag,parentless,leaf,hidden⟩ := geometry
  rw [tagEq] at nodeTag
  have buffer := GeneralBorrowRawWildcardWindowFunctionState.buffer_lookup (RawRootInvocation.machine #[] s.before)
    s.tracker s.fresh s.id s.entry output.child.tree s.slotFresh s.slotId s.slotEntry s.slotRoot allocation (Ne.symm s.separate)
  have slot : (machine s output allocation).memory.live.find? (fun row => row.1 == s.slotId) =
      some (s.slotId,{s.slotEntry with allocation := allocation}) := by
    unfold machine GeneralBorrowRawWildcardWindowFunctionState.enteredMachine
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  exact ⟨{
    output := output
    operation := run
    slotAllocation := allocation
    slotProperties := properties
    call := call
    child := child
    lookup := lookup
    runtime := finalRuntime
    positive := Classical.choice finalPositive
    activity := activity
    capacity := capacity
    growth := growth
    distinct := distinct
    roots := roots
    node := node
    nodePresent := nodePresent
    nodeTag := nodeTag
    parentless := parentless
    leaf := leaf
    hidden := hidden
    buffer := buffer
    slot := slot
    tracked := rfl
  },rfl,rfl⟩

/-- Every count uses the same original wildcard Initial. Actual ROOT argument
retagging and both Strong protector registrations are executed, not premises. -/
theorem initializes (s : Initial) (n : UInt64) : Nonempty (Packet s n) := by
  obtain ⟨output,run,allocation,call,properties⟩ := initializes_raw s n
  obtain ⟨packet,_,_⟩ := described s n output run allocation call properties
  exact ⟨packet⟩
end
end DuplicatePrefix.GeneralBorrowRawWildcardWindowInitialize
