import duplicate_prefix.CurrentCallLenReadCapability
import duplicate_prefix.CurrentCallLenArgumentCopy
import duplicate_prefix.GeneralBorrowSharedConstructorRuntime
import duplicate_prefix.GeneralBorrowConstructorChildActivity
import duplicate_prefix.GeneralBorrowFnEntryRegistrationRuntime
import duplicate_prefix.GeneralBorrowRawSharedFnEntry
import duplicate_prefix.GeneralBorrowFreshReadRegistration

namespace DuplicatePrefix.CurrentCallLenReadEntry
open Miri.Input Miri.MIR
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowExposureCardinality GeneralRangeMapOrigins GeneralRangeMapState
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend
open GeneralBorrowForestMixedLenBeforeReturn
open CurrentCallLenArgumentCopy
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend
open GeneralBorrowForestMixedLenBeforeReturn
open CurrentCallLenArgumentCopy
open GeneralBorrowProjection
open GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

private theorem registered_authority (tree : BorrowTree) (completion : Completion)
    (global : GlobalState) (frame : FrameState) (id : AllocId)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (fresh : GeneralBorrowProtector.Fresh tree global.nextPointerTag)
    (selected source reader : UniIndex) (location : LocationTree)
    (old : S05CurrentReadProtectorRelease.Authority tree completion global.protectedTags selected source reader location) :
    S05CurrentReadProtectorRelease.Authority tree completion
      (registered global frame id room).1.protectedTags selected source reader location := by
  have same : ∀ index node,tree.nodeAt index=some node →
      (registered global frame id room).1.protectedTags.contains node.tag=global.protectedTags.contains node.tag := by
    intro index node present
    exact ProtectorInsertion.contains_other global.protectedTags global.nextPointerTag node.tag .StrongProtector
      (fresh (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present)))
  have projection := GeneralBorrowProtector.normal_projection tree location global.protectedTags global.nextPointerTag .StrongProtector fresh
  obtain ⟨cap⟩ := old.2.1
  refine ⟨old.1,⟨⟨cap.component,?_⟩⟩,?_⟩
  · intro index support valid
    have projectionRegistered : source_normal_projection tree location (registered global frame id room).1.protectedTags =
        source_normal_projection tree location global.protectedTags := projection
    rw [projectionRegistered]
    exact cap.permissions index support valid
  · intro position root slot different index node present path
    rw [same index node present]
    exact old.2.2 position root slot different index node present path

/-- The actual shared helper uses a Read capability in its selected component;
mutable source rights are used only in the other physical roots. -/
theorem invoke (tree : BorrowTree) (completion : Completion) (global : GlobalState)
    (frame : FrameState) (id : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (model : CurrentCallResourceNormalization.ParentInterpretation tree completion)
    (distinct : tree.roots.toList.Nodup)
    (selectedPosition : Nat) (selected source reader : UniIndex) (selectedNode readerNode : TreeNode)
    (primaryBelow : ∀ root,tree.roots[0]?=some root → Below completion root source)
    (selectedSlot : tree.roots[selectedPosition]?=some selected)
    (selectedPresent : tree.nodes.get selected=some selectedNode) (sourcePath : Path tree selected source)
    (readerPresent : tree.nodes.get reader=some readerNode) (readerPath : Path tree selected reader)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (short : tree.nodes.size < 65536) (nodeRoom : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (owned : OwnedOn (S05CurrentReadProtectorRelease.Authority tree completion global.protectedTags selected source reader)
      offset (offset+len) tree.locations)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let registration := registered global frame id room
    let read := tree.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes offset) (Size.ofBytes len)
      .Read registration.1.protectedTags .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes offset) (.concrete readerNode.tag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true
    GeneralBorrowRawSharedFnEntry.operation tree global frame id readerNode.tag offset len .VisitChildrenOfAccessed =
      .ok ⟨registration.1,registration.2,global.nextPointerTag,read,child⟩ ∧
    read.status=.Completed ∧ child.outcome=.ok () ∧
    DuplicatePrefixBorrowContract.RuntimeFacts child.tree registration.1 ∧
    child.tree.locations.size=tree.locations.size ∧ child.tree.nodes.size≤tree.nodes.size+1 ∧
    ∃ childIndex,child.tree.indexOfTag global.nextPointerTag=some childIndex ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin child.tree childIndex .Read offset (offset+len) := by
  obtain ⟨allocated,held,_,registeredRuntime,nodeFresh,fresh⟩ :=
    GeneralBorrowFnEntryRegistrationRuntime.prepare tree global frame id room runtime
  let registration := registered global frame id room
  let read := tree.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registration.1.protectedTags .VisitChildrenOfAccessed
  have registeredOwned : OwnedOn (S05CurrentReadProtectorRelease.Authority tree completion registration.1.protectedTags selected source reader)
      offset (offset+len) tree.locations := by
    intro cursor valid positive upper lower
    exact registered_authority tree completion global frame id room nodeFresh selected source reader _
      (owned cursor valid positive upper lower)
  have noWrap : offset.toNat+len.toNat < 2^64 := Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt tree.locations.size.bytes)
  have endEq : (offset+len).toNat=offset.toNat+len.toNat := by simp only [UInt64.toNat_add,Nat.mod_eq_of_lt noWrap]
  have contract := CurrentCallLenReadCapability.access tree completion registration.1.protectedTags model distinct
    selectedPosition selected source reader selectedNode readerNode primaryBelow selectedSlot selectedPresent sourcePath readerPresent readerPath
    (Size.ofBytes offset) (Size.ofBytes len) offset (offset+len) registeredOwned runtime.formed.well
    (fun cursor valid => ⟨registeredRuntime.coherent cursor valid,registeredRuntime.formed.profile cursor valid,registeredRuntime.possible cursor valid⟩)
    bounds (Nat.le_refl _) (by change (offset+len).toNat ≤ (offset+len).toNat; exact Nat.le_refl _) short .VisitChildrenOfAccessed
  have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts read.tree registration.1 := by
    rw [contract.tree_eq]
    refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations tree _ registeredRuntime.formed.toGraphState,contract.well⟩,?_⟩,
      ?_,?_,⟨registeredRuntime.below.mapping,registeredRuntime.below.protectors⟩⟩
    · intro cursor valid
      exact ⟨(contract.runtime cursor valid).2.1.present,(contract.runtime cursor valid).2.1.vacant⟩
    · intro cursor valid
      exact (contract.runtime cursor valid).1
    · intro cursor valid
      exact (contract.runtime cursor valid).2.2
  have readerAfter : read.tree.nodeAt reader=some readerNode := by change read.tree.nodes.get reader=some readerNode; rw [contract.nodes];exact readerPresent
  have tagged := afterRuntime.formed.allocator.nodeTags reader readerNode readerAfter
  have freshAfter : GeneralBorrowTagMap.Fresh read.tree.tagMapping global.nextPointerTag := by rw [contract.tags];exact fresh
  have roomAfter : read.tree.nodes.size+1≤4294967295 := by rw [contract.nodes];exact nodeRoom
  have boundAfter : offset.toNat+len.toNat≤read.tree.locations.size.bytes.toNat := by rw [contract.capacity];exact bounds
  have tagBound : global.nextPointerTag.value.toNat<registration.1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag room
    change global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag global.nextPointerTag room).value.toNat
    omega
  have heldTag : registration.1.protectedTags.contains global.nextPointerTag=true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  obtain ⟨done,current,capacity,growth⟩ := GeneralBorrowSharedConstructorRuntime.construct read.tree registration.1 afterRuntime
    readerNode.tag global.nextPointerTag reader readerNode tagged readerAfter freshAfter roomAfter tagBound true heldTag offset len nonzero boundAfter
  obtain ⟨child,lookup,activity⟩ := GeneralBorrowConstructorChildActivity.Shared.construct read.tree registration.1 afterRuntime
    readerNode.tag global.nextPointerTag reader readerNode tagged readerAfter freshAfter roomAfter true offset len nonzero boundAfter
  refine ⟨?_,contract.completed,done,current,capacity.trans contract.capacity,?_,child,lookup,activity⟩
  · simp only [GeneralBorrowRawSharedFnEntry.operation,allocated,Except.bind,Except.pure,bind,pure]
    rfl
  · rw [contract.nodes] at growth
    exact growth


/-- Actual typed validation, argument copy and scoped Len frame installation,
with both operational certificates derived from the current narrow resources. -/
theorem actual_entry
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (exprTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (model : CurrentCallResourceNormalization.ParentInterpretation entry.allocation.extra completion)
    (distinct : entry.allocation.extra.roots.toList.Nodup)
    (selectedPosition : Nat) (selected source reader : UniIndex) (selectedNode readerNode : TreeNode)
    (primaryBelow : ∀ root,entry.allocation.extra.roots[0]?=some root → Below completion root source)
    (selectedSlot : entry.allocation.extra.roots[selectedPosition]?=some selected)
    (selectedPresent : entry.allocation.extra.nodes.get selected=some selectedNode)
    (sourcePath : Path entry.allocation.extra selected source)
    (readerPresent : entry.allocation.extra.nodes.get reader=some readerNode)
    (readerPath : Path entry.allocation.extra selected reader) (readerTag : readerNode.tag=exprTag)
    (short : entry.allocation.extra.nodes.size<65536) (nodeRoom : entry.allocation.extra.nodes.size+1≤4294967295)
    (owned : OwnedOn (S05CurrentReadProtectorRelease.Authority entry.allocation.extra completion tracker.global.protectedTags selected source reader)
      offset (offset+len) entry.allocation.extra.locations)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (allocationSize : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (localId : MIR.LocalId) (valid : localId < caller.locals.size) (old : Immediate Provenance)
    (live : caller.locals[localId].value = .live (.immediate old))
    (cached : caller.locals[localId].layout = some RootCompilerFacts.usizeLayout)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (presentFrame : (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current)
    (metadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView current)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get
      (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames caller machine)
        (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView current))) :
    let cfg := config options remaining span
    let state := Storage.withCurrent frames caller machine
    let destination := (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView
    let frame := LenEntry.rawFrame options state destination
    let postMachine := (LenPush.completed options.userRelevantCrates state destination current).machine
    let frameValid : 1 < frame.locals.size := by rw [LenEntry.raw_size]; decide
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let output := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let finalTree := finalTree entry.allocation.extra tracker exprTag offset len
    let afterFrame := TypedBorrowSteps.registeredFrame (LenInstall.resultFrame frame frameValid output) {} id tracker.global.nextPointerTag
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      LenHelper.resolved.callee LenHelper.body LenHelper.abi #[.Copy ⟨.immediate value,LenHelper.rawLayout⟩]
      false destination (.goto (some 3) .Continue) state =
      .ok () (Storage.withCurrent (frames.push caller)
        (LenDone.doneFrame {afterFrame with location := .unwinding LenEntryFacts.lenPreamble}) resultMachine) := by
  have treeBounds : offset.toNat+len.toNat≤entry.allocation.extra.locations.size.bytes.toNat := by rw [allocationSize];exact bounds
  have lenNonzero : len ≠ 0 := by intro zero;rw [zero] at positive;contradiction
  have result := invoke entry.allocation.extra completion tracker.global {} id runtime model distinct
    selectedPosition selected source reader selectedNode readerNode primaryBelow selectedSlot selectedPresent sourcePath readerPresent readerPath
    fresh short nodeRoom offset len lenNonzero owned treeBounds
  have readCompleted : (CurrentCallLenArgumentCopy.readOperation entry.allocation.extra tracker exprTag offset len).status=.Completed := by
    simpa only [readerTag,CurrentCallLenArgumentCopy.readOperation,registered,advanced,GlobalState.addProtector,TypedBorrowSteps.registeredGlobal] using result.2.1
  have childCompleted : (CurrentCallLenArgumentCopy.childOperation entry.allocation.extra tracker exprTag offset len).outcome=.ok () := by
    simpa only [readerTag,CurrentCallLenArgumentCopy.childOperation,CurrentCallLenArgumentCopy.readOperation,registered,advanced,GlobalState.addProtector,TypedBorrowSteps.registeredGlobal,GeneralBorrowFreshAnchor.sharedState,NestedConstruction.frozenRead] using result.2.2.1
  exact CurrentCallLenArgumentCopy.actual_entry options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len exprTag positive nonzero signedFits frames caller machine tracker enabled fresh readCompleted childCompleted
    bounds allocationSize localId valid old live cached noClocks ghost shallow cachedAddress present race thread index current active top presentFrame metadata cacheOrigins


end
end DuplicatePrefix.CurrentCallLenReadEntry

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallLenReadEntry.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved narrow Len FnEntry dependency {dependency}"
