import duplicate_prefix.CurrentCallPush
import duplicate_prefix.CurrentCallBoolWindow
import duplicate_prefix.S02SameDestinationUninitInitializedMutation
import duplicate_prefix.S02SameDestinationUninitInitializedBits
import duplicate_prefix.CandidateCurrentBoolUninitWrite
import duplicate_prefix.S05CompletedAncestryRangeWrite

/-! Bool destination protection after argument copying. The temporary
retagged place is used for writeUninit and discarded. Its child and protector
stay live until pop; the frame retains the original return destination. -/
namespace DuplicatePrefix.CurrentCallBoolProtection
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver ReturnProtection
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowFnEntryRegistration GeneralRangeMapOrigins
open S05CompletedAncestryReadMutable (Authority)
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Internal operational glue for arbitrary actual provenance and interior
windows. The enclosing consumer supplies these two tree steps from current raw
authority; the policy and metadata here are the real fixed Bool policy. -/
theorem retag_of_steps
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualRetagContext.Context options remaining span) (budget : Nat)
    (machine : Before) (tracker : MachineHooks.BorrowState)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (place : MPlaceTy Provenance) (layout : place.layout = RootCompilerFacts.boolLayout)
    (pointer : Pointer Provenance) (pointerEq : place.mplace.ptr = pointer.withOptionalProvenance)
    (id : AllocId) (offset : Nat)
    (binding : CandidateCallBindings.WindowBinding machine pointer id offset 1)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (race : machine.dataRace = none) (parentTree finalTree : BorrowTree)
    (readTree : (entry.allocation.extra.performBorrowAccessRange
      (CandidateCurrentWindowPointerChecks.extraOf pointer.provenance) (Size.ofBytes (UInt64.ofNat offset))
      (Size.ofBytes 1) .Read (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags
      .VisitChildrenOfAccessed).tree = parentTree)
    (readDone : (entry.allocation.extra.performBorrowAccessRange
      (CandidateCurrentWindowPointerChecks.extraOf pointer.provenance) (Size.ofBytes (UInt64.ofNat offset))
      (Size.ofBytes 1) .Read (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags
      .VisitChildrenOfAccessed).status = .Completed)
    (child : parentTree.newChild (Size.ofBytes (UInt64.ofNat offset))
      (CandidateCurrentWindowPointerChecks.extraOf pointer.provenance) tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes 1) ChildBorrow.fnEntryLocation)
      MachineHooks.protectionPolicy.outsidePermission MachineHooks.protectionPolicy.protector.isSome = ⟨finalTree,.ok ()⟩) :
    TypedRetag.retagPlace (config options remaining span).retag budget place MachineHooks.protectionPolicy
      (Storage.withCurrent frames frame machine) =
      .ok (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag)
        (borrowedState frames frame borrowFrame machine tracker fresh id entry finalTree) := by
  let h := (config options remaining span).retag
  let start := Storage.withCurrent frames frame (allocatedMachine machine tracker fresh)
  have allocatedBinding : CandidateCallBindings.WindowBinding start.machine pointer id offset (1 : UInt64).toNat := binding
  obtain ⟨check,resolve⟩ := CandidateCurrentWindowPointerChecks.actual_retag options remaining span ctx start pointer id offset 1
    allocatedBinding (by decide) (by decide)
  have frozen : h.typeIsFreeze place.layout.ty = pure true := by
    rw [layout]; exact ActualRetagContext.bool_freeze options remaining span ctx
  have inside := TypedRetagPolicyFields.inside_for_policy h budget place (Size.ofBytes 1)
    MachineHooks.protectionPolicy ChildBorrow.fnEntryLocation rfl ctx.source.precise frozen
  have reborrow := protected_reborrow_of_steps h budget place frames frame borrowFrame
    (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) rfl frameBorrow id entry (UInt64.ofNat offset) 1
    (CandidateCurrentWindowPointerChecks.extraOf pointer.provenance) tracker.global.nextPointerTag ChildBorrow.fnEntryLocation
    MachineHooks.protectionPolicy rfl rfl (by decide)
    (by rw [ctx.source.check,pointerEq];exact check)
    (by rw [ctx.source.resolve,pointerEq];exact resolve)
    (by rw [ctx.source.log]) inside .global ctx.globals (Eq.trans ctx.source.ensure ctx.ensure) ctx.synchronize present race
    parentTree finalTree readTree readDone child
  exact retag_place_of_reborrow h budget place MachineHooks.protectionPolicy (Size.ofBytes 1) Align.ONE
    (Storage.withCurrent frames frame machine) (borrowedState frames frame borrowFrame machine tracker fresh id entry finalTree)
    tracker enabled fresh id pointer.provenance (by rw [pointerEq];rfl)
    (ActualRetagContext.bool_size options remaining span ctx place layout) reborrow

/-- Actual Write through the fresh concrete child consumes raw authority while
retaining runtime/completion and the disjoint source's SAME authority. -/
theorem write_range (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (child : UniIndex) (node : TreeNode) (present : tree.nodes.get child = some node)
    (offset : UInt64) (bounds : offset.toNat+1 ≤ tree.locations.size.bytes.toNat)
    (short : tree.nodes.size < 65536)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags child)
      offset (offset+1) tree.locations)
    (source : UniIndex) (lower upper : UInt64)
    (disjoint : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      point.toNat < offset.toNat ∨ (offset+1).toNat ≤ point.toNat)
    (sourceOwned : GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags source)
      lower upper tree.locations) :
    let written := tree.performBorrowAccessRange (.concrete node.tag) (Size.ofBytes offset) (Size.ofBytes 1)
      .Write global.protectedTags .VisitChildrenOfAccessed
    written.status = .Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts written.tree global ∧
      Completes written.tree completion ∧ written.tree.nodes = tree.nodes ∧
      written.tree.locations.size = tree.locations.size ∧
      GeneralRangeMapOrigins.OwnedOn
        (S05CompletedAncestryReadMutable.Authority written.tree completion global.protectedTags source)
        lower upper written.tree.locations := by
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ :=
    CandidateCurrentWindowAuthority.root_path tree runtime.formed.toGraphState child node present
  obtain ⟨depth⟩ := runtime.formed.depth
  have mapped := (complete.2.2.2.2.1 child node present).1
  have range := GeneralBorrowConcreteRangeEntry.access tree global.protectedTags node.tag child mapped
    (Size.ofBytes offset) (Size.ofBytes 1) .Write .VisitChildrenOfAccessed
    (S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags child)
    (fun _ => True)
    (fun location => GeneralBorrowExposureCardinality.LocationCoherent tree location global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (fun _ _ => True) (fun _ _ => trivial) (fun _ => trivial)
    (by
      intro location authority representation range
      have row := S05CompletedAncestryConcreteWrite.access tree completion location global.protectedTags complete
        runtime.formed.toGraphState depth order position root child rootNode slot rootAt path
        (fun index current found _ below => (authority index current found).1 below)
        (fun index current found _ outside => (authority index current found).2 outside)
        (fun _ _ _ _ index current found _ below => (authority index current found).1 below)
        (fun _ _ _ _ index current found _ outside => (authority index current found).2 outside)
        representation.1 representation.2.1 representation.2.2 short .VisitChildrenOfAccessed range
      exact ⟨row.1,trivial,⟨row.2.1,row.2.2.1,row.2.2.2.1⟩,trivial⟩)
    offset (offset+1) owned runtime.formed.well
    (fun cursor valid => ⟨runtime.coherent cursor valid,runtime.formed.profile cursor valid,runtime.possible cursor valid⟩)
    bounds (Nat.le_refl _) (Nat.le_refl _)
  let written := tree.performBorrowAccessRange (.concrete node.tag) (Size.ofBytes offset) (Size.ofBytes 1)
    .Write global.protectedTags .VisitChildrenOfAccessed
  have same : written.tree = {tree with locations := written.tree.locations} := range.tree_eq
  have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts written.tree global := by
    rw [same]
    refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations tree _ runtime.formed.toGraphState,
      range.well⟩,?_⟩,?_,?_,⟨runtime.below.mapping,runtime.below.protectors⟩⟩
    · intro cursor valid
      exact ⟨(range.runtime cursor valid).2.1.present,(range.runtime cursor valid).2.1.vacant⟩
    · intro cursor valid
      exact (range.runtime cursor valid).1
    · intro cursor valid
      exact (range.runtime cursor valid).2.2
  have afterComplete : Completes written.tree completion := by
    rw [same]
    exact CandidateCurrentJointRawReplacement.completes tree completion _ complete
  have framed := GeneralBorrowRangeOutsideOwned.owned
    (S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags source)
    tree (.concrete node.tag) (Size.ofBytes offset) (Size.ofBytes 1) .Write global.protectedTags
    .VisitChildrenOfAccessed runtime.formed.well bounds lower upper disjoint sourceOwned
  refine ⟨range.completed,afterRuntime,afterComplete,range.nodes,range.capacity,?_⟩
  intro cursor valid positive start stop index current found
  exact framed cursor valid positive start stop index current (by rw [←range.nodes];exact found)

def returnTree {before tracker frame argument len place call data}
    (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data) : BorrowTree :=
  if call.sourceId = call.returnId then raw.output.child.tree else raw.returnAllocation.extra

def returnCompletion {before tracker frame argument len place call data}
    (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data) : Completion :=
  if call.sourceId = call.returnId then
    S05ConcreteProtectedChildCompletion.extend raw.sourcePrecise.completion raw.child raw.sourcePointer.grant
  else raw.returnPrecise.completion

/-- The current return origin and graph facts survive the actual source retag.
Only original representation/resources are consumed, including global high-water. -/
theorem return_ready {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState)
    (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data) :
    DuplicatePrefixBorrowContract.RuntimeFacts (returnTree raw) raw.output.global ∧
      Completes (returnTree raw) (returnCompletion raw) ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder (returnTree raw) ∧
      ∃ node, (returnTree raw).nodes.get raw.returnPointer.grant = some node ∧
        (match raw.returnPointer.value.provenance with
        | .concrete _ tag => tag = node.tag
        | .wildcard => node.isExposed = true) := by
  have live := CandidateCurrentLiveRuntime.live options limits remaining before tracker len input.machine.state input.machine.resources
  obtain ⟨returnRuntime,returnOrder,_,_,_,_⟩ := live call.returnId raw.returnAllocation raw.returnPresent
  obtain ⟨other,otherPresent,binds⟩ := input.actual.instances raw.returnPointer
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? raw.returnPointerAt))
  rw [raw.returnId] at otherPresent
  have equal := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList input.machine.worldIds
    call.returnId other raw.returnAllocation otherPresent raw.returnPresent
  subst other
  obtain ⟨node,nodeAt,_,binding⟩ := binds
  have provenance : match raw.returnPointer.value.provenance with
      | .concrete _ tag => tag = node.tag
      | .wildcard => node.isExposed = true := by
    cases h : raw.returnPointer.value.provenance with
    | concrete id tag =>
      simp only [h] at binding
      exact binding.2
    | wildcard => simpa only [h] using binding
  by_cases same : call.sourceId = call.returnId
  · have allocationEq := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList input.machine.worldIds
      call.sourceId raw.sourceAllocation raw.returnAllocation raw.sourcePresent (by rw [same];exact raw.returnPresent)
    obtain ⟨next,nextAt,tagEq,_,exposedEq⟩ := raw.oldNodes raw.returnPointer.grant node (by rw [allocationEq];exact nodeAt)
    refine ⟨by simpa [returnTree,same] using raw.runtime,
      by simpa [returnTree,returnCompletion,same] using raw.completes,
      by simpa [returnTree,same] using raw.outputOrder,next,by simpa [returnTree,same] using nextAt,?_⟩
    cases h : raw.returnPointer.value.provenance with
    | concrete id tag =>
      have oldTag : tag = node.tag := by simpa only [h] using provenance
      exact oldTag.trans tagEq.symm
    | wildcard => simpa only [h] using (show next.isExposed = true from exposedEq.trans (by simpa [h] using provenance))
  · obtain ⟨_,_,_,registeredRuntime,_,_⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare
      raw.returnAllocation.extra tracker.global frame call.sourceId raw.tagRoom returnRuntime
    have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts raw.returnAllocation.extra raw.output.global := by
      rw [raw.outputGlobal];exact registeredRuntime
    obtain ⟨allocation,present,completed,_,_⟩ := input.machine.completed call.returnId raw.returnPrecise raw.returnPreciseAt
    have allocationEq := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList input.machine.worldIds
      call.returnId allocation raw.returnAllocation present raw.returnPresent
    subst allocation
    exact ⟨by simpa [returnTree,same] using afterRuntime,
      by simpa [returnTree,returnCompletion,same] using completed,
      by simpa [returnTree,same] using returnOrder,node,by simpa [returnTree,same] using nodeAt,provenance⟩

private theorem node_margin {options limits remaining before tracker len}
    (resources : DuplicatePrefixCallSpecification.Resources options limits remaining before tracker len)
    (id : AllocId) (allocation : Allocation Provenance BorrowTree)
    (present : Present (ActualWorld before) id allocation) : allocation.extra.nodes.size+16 < 65536 := by
  simp only [Present,ActualWorld,Array.toList_map] at present
  obtain ⟨⟨oldId,entry⟩,member,equal⟩ := List.mem_map.mp present
  rcases Prod.mk.inj equal with ⟨rfl,rfl⟩
  exact resources.nodeRoom (oldId,entry) member

theorem return_budget {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState)
    (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data) :
    raw.output.global.nextPointerTag.value < 18446744073709551615 ∧
      (returnTree raw).nodes.size+1 ≤ 4294967295 ∧ (returnTree raw).nodes.size+1 < 65536 := by
  have originalRoom := input.machine.resources.tagRoom
  have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag raw.tagRoom
  have next : raw.output.global.nextPointerTag = TypedRetagEmpty.successorTag tracker.global.nextPointerTag raw.tagRoom := by
    rw [raw.outputGlobal]
    rfl
  have tagRoom : raw.output.global.nextPointerTag.value < 18446744073709551615 := by
    rw [next]
    apply UInt64.lt_iff_toNat_lt.mpr
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag raw.tagRoom).value.toNat < 18446744073709551615
    omega
  have sourceMargin := node_margin input.machine.resources call.sourceId raw.sourceAllocation raw.sourcePresent
  have returnMargin := node_margin input.machine.resources call.returnId raw.returnAllocation raw.returnPresent
  refine ⟨tagRoom,?_⟩
  by_cases same : call.sourceId = call.returnId
  · have growth := raw.outputGrowth
    simp only [returnTree,same,ite_true]
    omega
  · simp only [returnTree,same,ite_false]
    omega

theorem original_windows {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState)
    (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (positive : 0 < len.toNat) :
    CandidateCallBindings.WindowBinding before raw.sourcePointer.value call.sourceId call.sourceOffset len.toNat ∧
      CandidateCallBindings.WindowBinding before raw.returnPointer.value call.returnId call.returnOffset 1 := by
  constructor
  · rcases input.actual.sourceAddress with empty | ⟨_,bits,argumentEq,loan,pointer,loanAt,pointerAt,valueEq,_,window⟩
    · simp [empty.1] at positive
    have bitsEq : bits = raw.sourcePointer.value := DuplicatePrefixSliceArgument.Argument.pointer.inj (argumentEq.symm.trans raw.argument_eq)
    rw [bitsEq,input.actual.length] at window
    exact window
  · obtain ⟨_,bits,_,loan,pointer,loanAt,pointerAt,valueEq,_,window⟩ := input.actual.returnAddress
    have loanEq : loan = raw.returnLoan := Option.some.inj (loanAt.symm.trans raw.returnLoanAt)
    subst loan
    have pointerEq : pointer = raw.returnPointer := Option.some.inj (pointerAt.symm.trans raw.returnPointerAt)
    subst pointer
    rw [←valueEq] at window
    exact window

private theorem window_allocation {before pointer id offset length allocation}
    (ids : ((ActualWorld before).toList.map Prod.fst).Nodup)
    (binding : CandidateCallBindings.WindowBinding before pointer id offset length)
    (present : Present (ActualWorld before) id allocation) :
    offset+length ≤ allocation.len ∧ allocation.len < 2^64 := by
  obtain ⟨entry,base,live,_,_,room,bounds,_,_,_⟩ := binding
  have entryPresent : Present (ActualWorld before) id entry.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(id,entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),rfl⟩
  have same := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList ids id entry.allocation allocation entryPresent present
  rw [same] at room bounds
  exact ⟨bounds,by omega⟩

private theorem return_capacity {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState) (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data) :
    (returnTree raw).locations.size = raw.returnAllocation.extra.locations.size := by
  by_cases same : call.sourceId = call.returnId
  · have allocationEq := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList input.machine.worldIds
      call.sourceId raw.sourceAllocation raw.returnAllocation raw.sourcePresent (by rw [same];exact raw.returnPresent)
    simpa only [returnTree,same,ite_true,allocationEq] using raw.outputCapacity
  · simp only [returnTree,same,ite_false]

/-- Normalized original windows give nonwrapping endpoints and the physical
source/return disjointness needed by the second protected child. -/
theorem endpoints {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState) (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (positive : 0 < len.toNat) :
    (UInt64.ofNat call.sourceOffset).toNat = call.sourceOffset ∧
      (UInt64.ofNat call.returnOffset).toNat = call.returnOffset ∧
      (UInt64.ofNat call.sourceOffset+len).toNat = call.sourceOffset+len.toNat ∧
      (UInt64.ofNat call.returnOffset+1).toNat = call.returnOffset+1 ∧
      (UInt64.ofNat call.returnOffset).toNat+1 ≤ (returnTree raw).locations.size.bytes.toNat ∧
      (call.sourceId = call.returnId → ∀ point : UInt64,
        (UInt64.ofNat call.sourceOffset).toNat ≤ point.toNat → point.toNat < (UInt64.ofNat call.sourceOffset+len).toNat →
        point.toNat < (UInt64.ofNat call.returnOffset).toNat ∨ (UInt64.ofNat call.returnOffset+1).toNat ≤ point.toNat) := by
  obtain ⟨sourceWindow,returnWindow⟩ := original_windows input frame raw positive
  obtain ⟨sourceBounds,sourceRoom⟩ := window_allocation input.machine.worldIds sourceWindow raw.sourcePresent
  obtain ⟨returnBounds,returnRoom⟩ := window_allocation input.machine.worldIds returnWindow raw.returnPresent
  have sourceOffsetEq : (UInt64.ofNat call.sourceOffset).toNat = call.sourceOffset := by simp [Nat.mod_eq_of_lt (by omega : call.sourceOffset<2^64)]
  have returnOffsetEq : (UInt64.ofNat call.returnOffset).toNat = call.returnOffset := by simp [Nat.mod_eq_of_lt (by omega : call.returnOffset<2^64)]
  have sourceSum : (UInt64.ofNat call.sourceOffset+len).toNat = call.sourceOffset+len.toNat := by
    rw [UInt64.toNat_add,sourceOffsetEq,Nat.mod_eq_of_lt (by omega)]
  have returnSum : (UInt64.ofNat call.returnOffset+1).toNat = call.returnOffset+1 := by
    rw [UInt64.toNat_add,returnOffsetEq]
    change (call.returnOffset+1)%2^64 = call.returnOffset+1
    exact Nat.mod_eq_of_lt (by omega)
  have live := CandidateCurrentLiveRuntime.live options limits remaining before tracker len input.machine.state input.machine.resources
  have capacity := (live call.returnId raw.returnAllocation raw.returnPresent).2.2.2.2.2
  refine ⟨sourceOffsetEq,returnOffsetEq,sourceSum,returnSum,?_,?_⟩
  · rw [return_capacity input frame raw,capacity,returnOffsetEq]
    exact returnBounds
  · intro same point lower upper
    apply Classical.byContradiction
    intro bad
    rw [sourceOffsetEq] at lower
    rw [sourceSum] at upper
    have overlapSource : Window call.sourceId call.sourceOffset call.length (call.sourceId,point.toNat) :=
      ⟨rfl,lower,by rw [input.actual.length];exact upper⟩
    have overlapReturn : Window call.returnId call.returnOffset 1 (call.sourceId,point.toNat) := by
      refine ⟨same,?_,?_⟩
      all_goals simp only [returnOffsetEq,returnSum] at bad;omega
    exact source_return_disjoint data.interpretation call input.joint.contents input.claims
      (call.sourceId,point.toNat) overlapSource overlapReturn

/-- Actual second retag output, before its uninitializing Write. The source
right refers to the actual shared tree when the allocations agree. -/
structure Borrowed {before tracker frame argument len place call data}
    (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data) where
  output : GeneralBorrowForestFnEntry.Output
  child : UniIndex
  actual : CandidateCurrentFnEntryRaw.operation (returnTree raw) raw.output.global raw.output.frame
    call.returnId raw.returnPointer.value.provenance (UInt64.ofNat call.returnOffset) 1 = .ok output
  tag : output.tag = raw.output.global.nextPointerTag
  readCompleted : output.access.status = .Completed
  childCompleted : output.child.outcome = .ok ()
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global
  metadata : CandidateCurrentFnEntryRaw.Metadata (returnTree raw) output.child.tree
  childLookup : output.child.tree.indexOfTag output.tag = some child
  completes : Completes output.child.tree
    (S05ConcreteProtectedChildCompletion.extend (returnCompletion raw) child raw.returnPointer.grant)
  boolOwned : GeneralRangeMapOrigins.OwnedOn
    (S05CompletedAncestryReadMutable.Authority output.child.tree
      (S05ConcreteProtectedChildCompletion.extend (returnCompletion raw) child raw.returnPointer.grant)
      output.global.protectedTags child)
    (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) output.child.tree.locations
  sourceOwned :
    let tree := if call.sourceId = call.returnId then output.child.tree else raw.output.child.tree
    let completion := if call.sourceId = call.returnId then
      S05ConcreteProtectedChildCompletion.extend (returnCompletion raw) child raw.returnPointer.grant
      else S05ConcreteProtectedChildCompletion.extend raw.sourcePrecise.completion raw.child raw.sourcePointer.grant
    GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority tree completion output.global.protectedTags raw.child)
      (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) tree.locations

private theorem framed_borrow (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (pointer : PointerInstance) (sourceNode : TreeNode)
    (sourcePresent : tree.nodes.get pointer.grant = some sourceNode)
    (provenance : match pointer.value.provenance with
      | .concrete _ tag => tag = sourceNode.tag
      | .wildcard => sourceNode.isExposed = true)
    (tagRoom : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295) (short : tree.nodes.size < 65536)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags pointer.grant) offset (offset+len) tree.locations)
    (target : UniIndex) (targetNode : TreeNode) (targetPresent : tree.nodes.get target = some targetNode)
    (boolOffset boolLen : UInt64) (boolBounds : boolOffset.toNat+boolLen.toNat ≤ tree.locations.size.bytes.toNat)
    (disjoint : ∀ point : UInt64,  boolOffset.toNat ≤ point.toNat → point.toNat < (boolOffset+boolLen).toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat)
    (boolOwned : OwnedOn (Authority tree completion global.protectedTags target) boolOffset (boolOffset+boolLen) tree.locations) :
    ∃ output,  CandidateCurrentFnEntryRaw.operation tree global frame allocation pointer.value.provenance offset len = .ok output ∧
      output.tag = global.nextPointerTag ∧ output.global = (registered global frame allocation tagRoom).1 ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      output.child.tree.indexOfTag targetNode.tag = some target ∧
      ∃ child,  output.child.tree.indexOfTag output.tag = some child ∧
        Completes output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child pointer.grant) ∧
        OwnedOn (Authority output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child pointer.grant)
          output.global.protectedTags child) offset (offset+len) output.child.tree.locations ∧
        OwnedOn (Authority output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child pointer.grant)
          output.global.protectedTags target) boolOffset (boolOffset+boolLen) output.child.tree.locations := by
  obtain ⟨position, root, rootNode, slot, rootAt, path⟩ :=
    CandidateCurrentWindowAuthority.root_path tree runtime.formed.toGraphState pointer.grant sourceNode sourcePresent
  cases actual : pointer.value.provenance with
  | concrete id tag =>
    have sameTag : tag = sourceNode.tag := by simpa [actual] using provenance
    obtain ⟨output, ok, tagEq, globalEq, _, readDone, childDone, afterRuntime, _, _, _, _, boolLookup,
      child, childLookup, _, afterComplete, sourceOwned, boolAfter⟩ :=
      S05ConcreteFnEntryDisjoint.invoke_window tree global frame allocation completion runtime complete order position root pointer.grant
        rootNode sourceNode slot rootAt sourcePresent path tagRoom nodeRoom short offset len nonzero bounds owned
        target targetNode targetPresent boolOffset boolLen boolBounds disjoint boolOwned
    exact ⟨output, by simpa [CandidateCurrentFnEntryRaw.operation, actual, sameTag] using ok, tagEq, globalEq, readDone, childDone, afterRuntime,
      boolLookup, child, childLookup, afterComplete, sourceOwned, boolAfter⟩
  | wildcard =>
    have exposed : sourceNode.isExposed = true := by simpa [actual] using provenance
    obtain ⟨output, ok, tagEq, globalEq, _, readDone, childDone, afterRuntime, _, _, _, _, boolLookup,
      child, childLookup, _, afterComplete, sourceOwned, boolAfter⟩ :=
      S05WildcardFnEntryRaw.invoke_window tree global frame allocation completion runtime complete order position root pointer.grant
        rootNode sourceNode slot rootAt sourcePresent exposed path tagRoom nodeRoom short offset len nonzero bounds owned
        target targetNode targetPresent boolOffset boolLen boolBounds disjoint boolOwned
    exact ⟨output, by simpa [CandidateCurrentFnEntryRaw.operation, actual] using ok, tagEq, globalEq, readDone, childDone, afterRuntime,
      boolLookup, child, childLookup, afterComplete, sourceOwned, boolAfter⟩

theorem borrow {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState) (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (positive : 0 < len.toNat) : Nonempty (Borrowed raw) := by
  obtain ⟨runtime,complete,order,node,nodeAt,provenance⟩ := return_ready input frame raw
  obtain ⟨tagRoom,nodeRoom,short⟩ := return_budget input frame raw
  obtain ⟨_,_,_,_,bounds,disjoint⟩ := endpoints input frame raw positive
  obtain ⟨output,actual,tag,globalEq,readDone,childDone,afterRuntime,child,lookup,afterComplete,childOwned,metadata,_⟩ :=
    CandidateCurrentFnEntryRaw.source_only (returnTree raw) raw.output.global raw.output.frame call.returnId
      (returnCompletion raw) runtime complete order raw.returnPointer node nodeAt provenance tagRoom nodeRoom (by omega)
      (UInt64.ofNat call.returnOffset) 1 (by decide) bounds raw.boolOwned
  have sourceAfter :
      let tree := if call.sourceId = call.returnId then output.child.tree else raw.output.child.tree
      let completion := if call.sourceId = call.returnId then
        S05ConcreteProtectedChildCompletion.extend (returnCompletion raw) child raw.returnPointer.grant
        else S05ConcreteProtectedChildCompletion.extend raw.sourcePrecise.completion raw.child raw.sourcePointer.grant
      GeneralRangeMapOrigins.OwnedOn
        (S05CompletedAncestryReadMutable.Authority tree completion output.global.protectedTags raw.child)
        (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) tree.locations := by
    by_cases same : call.sourceId = call.returnId
    · obtain ⟨sourceNode,sourceAt⟩ := (raw.completes.2.2.2.2.2.2 raw.child raw.sourcePointer.grant
        (S05ConcreteProtectedChildCompletion.child_edge raw.sourcePrecise.completion raw.child raw.sourcePointer.grant)).1
      have sourceCurrent : (returnTree raw).nodes.get raw.child = some sourceNode := by simpa [returnTree,same] using sourceAt
      have sourceBounds : (UInt64.ofNat call.sourceOffset).toNat+len.toNat ≤ (returnTree raw).locations.size.bytes.toNat := by
        obtain ⟨sourceWindow,_⟩ := original_windows input frame raw positive
        have physical := (window_allocation input.machine.worldIds sourceWindow raw.sourcePresent).1
        have live := CandidateCurrentLiveRuntime.live options limits remaining before tracker len input.machine.state input.machine.resources
        have capacity := (live call.sourceId raw.sourceAllocation raw.sourcePresent).2.2.2.2.2
        have offsetEq := (endpoints input frame raw positive).1
        simpa only [returnTree,same,ite_true,raw.outputCapacity,capacity,offsetEq] using physical
      have sourceOwned : GeneralRangeMapOrigins.OwnedOn
          (S05CompletedAncestryReadMutable.Authority (returnTree raw) (returnCompletion raw) raw.output.global.protectedTags raw.child)
          (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) (returnTree raw).locations := by
        simpa only [returnTree,returnCompletion,same,ite_true] using raw.sourceOwned
      obtain ⟨other,otherActual,_,_,_,_,_,_,otherChild,otherLookup,_,_,framed⟩ :=
        framed_borrow (returnTree raw) raw.output.global raw.output.frame call.returnId
          (returnCompletion raw) runtime complete order raw.returnPointer node nodeAt provenance tagRoom nodeRoom (by omega)
          (UInt64.ofNat call.returnOffset) 1 (by decide) bounds raw.boolOwned raw.child sourceNode sourceCurrent
          (UInt64.ofNat call.sourceOffset) len sourceBounds (disjoint same) sourceOwned
      have sameOutput : other = output := Except.ok.inj (otherActual.symm.trans actual)
      subst other
      have sameChild : otherChild = child := Option.some.inj (otherLookup.symm.trans lookup)
      subst otherChild
      simpa only [same,ite_true] using framed
    · have flags : ∀ index current, raw.output.child.tree.nodes.get index = some current →
          output.global.protectedTags.contains current.tag = raw.output.global.protectedTags.contains current.tag := by
        intro index current found
        have older := GeneralBorrowParentTagInvariant.parent_below_fresh raw.output.child.tree raw.output.global raw.runtime index current found
        have different : current.tag ≠ raw.output.global.nextPointerTag := by intro equal;rw [equal] at older;exact UInt64.lt_irrefl _ older
        rw [globalEq]
        exact ProtectorInsertion.contains_other raw.output.global.protectedTags raw.output.global.nextPointerTag current.tag .StrongProtector different
      simp only [same,ite_false]
      intro cursor valid nonzero start stop index current found
      rw [flags index current found]
      exact raw.sourceOwned cursor valid nonzero start stop index current found
  exact ⟨⟨output,child,actual,tag,readDone,childDone,afterRuntime,metadata,lookup,afterComplete,childOwned,sourceAfter⟩⟩

/-- Actual Bool retag after the scoped argument pair, from the original proposal
and the retained typed source outcome. No post-state proposal or retag-success
premise is supplied. The surrounding entry trace determines the current frame. -/
theorem retag_after_source
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (retagCtx : ActualRetagContext.Context options (remaining+1) span)
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frames : Array CompilerFrameContext.ActualFrame) (initialFrame : CompilerFrameContext.ActualFrame)
    (initialBorrow : FrameState)
    (source : CurrentCallReferenceEntry.ViewedOutcome options remaining span ctx before tracker frames initialFrame initialBorrow
      argument len place call data .FnEntry true)
    (frame : CompilerFrameContext.ActualFrame)
    (frameBorrow : frame.extra.borrowTracker = some source.base.raw.output.frame)
    (positive : 0 < len.toNat) :
    ∃ borrowed : Borrowed source.base.raw,
      ∃ physical : CandidateCurrentBoolUninitWrite.PhysicalWindow (CurrentCallBoolWindow.after source) place,
      ∃ room : source.base.raw.output.global.nextPointerTag.value < 18446744073709551615,
        physical.id = call.returnId ∧ physical.pointer = source.base.raw.returnPointer.value ∧
        physical.offset = UInt64.ofNat call.returnOffset ∧
        physical.entry.allocation.extra = returnTree source.base.raw ∧
        TypedRetag.retagPlace (config options (remaining+1) span).retag limits.retag place MachineHooks.protectionPolicy
          (Storage.withCurrent frames frame (CurrentCallBoolWindow.after source)) =
          .ok (TypedRetagGeneric.retaggedPlace place call.returnId source.base.raw.output.global.nextPointerTag)
            (borrowedState frames frame source.base.raw.output.frame (CurrentCallBoolWindow.after source)
              ⟨source.base.raw.output.global,tracker.retagMode⟩ room call.returnId physical.entry borrowed.output.child.tree) := by
  let raw := source.base.raw
  let machine := CurrentCallBoolWindow.after source
  let currentTracker : MachineHooks.BorrowState := ⟨raw.output.global,tracker.retagMode⟩
  obtain ⟨borrowed⟩ := borrow input initialBorrow raw positive
  obtain ⟨physical,idEq,pointerEq,offsetEq,binding⟩ := CurrentCallBoolWindow.after_source options limits remaining span ctx
    before tracker argument len place call data input frames initialFrame initialBorrow source
  have room := (return_budget input initialBorrow raw).1
  obtain ⟨boolEntry,boolLive,extra⟩ := source.boolInstalled
  have physicalLive : machine.memory.live.find? (fun row => row.1 == call.returnId) = some (call.returnId,physical.entry) := by
    simpa only [idEq] using physical.live
  have sameEntry : physical.entry = boolEntry := (Prod.mk.inj (Option.some.inj (physicalLive.symm.trans boolLive))).2
  have treeEq : physical.entry.allocation.extra = returnTree raw := by
    rw [sameEntry]
    exact extra
  have outputEq : borrowed.output = CurrentCallTypedFnEntry.literal physical.entry.allocation.extra raw.output.global raw.output.frame
      call.returnId room raw.returnPointer.value.provenance (UInt64.ofNat call.returnOffset) 1 := by
    apply Except.ok.inj
    exact borrowed.actual.symm.trans (by rw [treeEq];exact CurrentCallTypedFnEntry.literal_operation _ _ _ _ room _ _ _)
  have readDone := borrowed.readCompleted
  have childDone := borrowed.childCompleted
  rw [outputEq] at readDone childDone
  let accessed := physical.entry.allocation.extra.performBorrowAccessRange
    (CandidateCurrentWindowPointerChecks.extraOf raw.returnPointer.value.provenance) (Size.ofBytes (UInt64.ofNat call.returnOffset))
    (Size.ofBytes 1) .Read (registered raw.output.global raw.output.frame call.returnId room).1.protectedTags .VisitChildrenOfAccessed
  have childEq : accessed.tree.newChild (Size.ofBytes (UInt64.ofNat call.returnOffset))
      (CandidateCurrentWindowPointerChecks.extraOf raw.returnPointer.value.provenance) raw.output.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes 1) ChildBorrow.fnEntryLocation)
      MachineHooks.protectionPolicy.outsidePermission MachineHooks.protectionPolicy.protector.isSome =
      ⟨borrowed.output.child.tree,.ok ()⟩ := by
    rw [outputEq]
    change (CurrentCallTypedFnEntry.literal _ _ _ _ _ _ _ _).child = ⟨(CurrentCallTypedFnEntry.literal _ _ _ _ _ _ _ _).child.tree,.ok ()⟩
    cases found : (CurrentCallTypedFnEntry.literal physical.entry.allocation.extra raw.output.global raw.output.frame
        call.returnId room raw.returnPointer.value.provenance (UInt64.ofNat call.returnOffset) 1).child with
    | mk final outcome =>
      rw [found] at childDone
      cases childDone
      rfl
  have race : machine.dataRace = none := input.machine.settings.noDataRace
  refine ⟨borrowed,physical,room,idEq,pointerEq,offsetEq,treeEq,?_⟩
  exact retag_of_steps options (remaining+1) span retagCtx limits.retag machine currentTracker frames frame raw.output.frame rfl frameBorrow
    place physical.layout raw.returnPointer.value (by rw [←pointerEq];exact physical.physicalPointer)
    call.returnId call.returnOffset binding physical.entry physicalLive room race accessed.tree borrowed.output.child.tree rfl
    (by simpa only [CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,accessed,currentTracker,
      registered,GeneralBorrowFnEntryRegistration.advanced,allocatedTracker,registeredGlobal,GlobalState.addProtector,ite_true] using readDone) childEq

private theorem prepared_return {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState) (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (positive : 0 < len.toNat) :
    let room := (return_budget input frame raw).1
    let literal := CurrentCallTypedFnEntry.literal (returnTree raw) raw.output.global raw.output.frame call.returnId room
      raw.returnPointer.value.provenance (UInt64.ofNat call.returnOffset) 1
    DuplicatePrefixBorrowContract.RuntimeFacts literal.access.tree literal.global ∧
      Completes literal.access.tree (returnCompletion raw) ∧
      literal.access.tree.nodes = (returnTree raw).nodes ∧
      literal.access.tree.tagMapping = (returnTree raw).tagMapping ∧
      literal.access.tree.locations.size = (returnTree raw).locations.size := by
  obtain ⟨runtime,complete,order,node,nodeAt,provenance⟩ := return_ready input frame raw
  obtain ⟨room,_,short⟩ := return_budget input frame raw
  have bounds := (endpoints input frame raw positive).2.2.2.2.1
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ :=
    CandidateCurrentWindowAuthority.root_path (returnTree raw) runtime.formed.toGraphState raw.returnPointer.grant node nodeAt
  cases prov : raw.returnPointer.value.provenance with
  | concrete id tag =>
    have tagEq : tag = node.tag := by simpa [prov] using provenance
    obtain ⟨_,afterRuntime,afterComplete,_,nodes,_,tags,capacity⟩ := S05ConcreteFnEntryRaw.prepare_read
      (returnTree raw) raw.output.global raw.output.frame call.returnId (returnCompletion raw) runtime complete order
      position root raw.returnPointer.grant rootNode node slot rootAt nodeAt path room (UInt64.ofNat call.returnOffset) 1
      bounds raw.boolOwned (by omega) .VisitChildrenOfAccessed
    simpa only [CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,
      prov,tagEq] using And.intro afterRuntime (And.intro afterComplete (And.intro nodes (And.intro tags capacity)))
  | wildcard =>
    have exposed : node.isExposed = true := by simpa [prov] using provenance
    obtain ⟨_,afterRuntime,afterComplete,_,nodes,_,tags,capacity⟩ := S05WildcardFnEntryRaw.prepare_read
      (returnTree raw) raw.output.global raw.output.frame call.returnId (returnCompletion raw) runtime complete order
      position root raw.returnPointer.grant rootNode node slot rootAt nodeAt exposed path room (UInt64.ofNat call.returnOffset) 1
      bounds raw.boolOwned (by omega) .VisitChildrenOfAccessed
    simpa only [CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,
      prov] using And.intro afterRuntime (And.intro afterComplete (And.intro nodes (And.intro tags capacity)))

/-- The child's stored tag comes from the real constructor, not inverse lookup. -/
theorem borrowed_node {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState) (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (positive : 0 < len.toNat) (borrowed : Borrowed raw) :
    ∃ node, borrowed.output.child.tree.nodes.get borrowed.child = some node ∧ node.tag = borrowed.output.tag := by
  obtain ⟨runtime,_,_,parentNode,parentAt,provenance⟩ := return_ready input frame raw
  obtain ⟨room,nodeRoom,_⟩ := return_budget input frame raw
  let literal := CurrentCallTypedFnEntry.literal (returnTree raw) raw.output.global raw.output.frame call.returnId room
    raw.returnPointer.value.provenance (UInt64.ofNat call.returnOffset) 1
  have outputEq : borrowed.output = literal := Except.ok.inj
    (borrowed.actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ room _ _ _))
  obtain ⟨readRuntime,readComplete,readNodes,readTags,readCapacity⟩ := prepared_return input frame raw positive
  change DuplicatePrefixBorrowContract.RuntimeFacts literal.access.tree literal.global at readRuntime
  change Completes literal.access.tree (returnCompletion raw) at readComplete
  change literal.access.tree.nodes = (returnTree raw).nodes at readNodes
  change literal.access.tree.tagMapping = (returnTree raw).tagMapping at readTags
  change literal.access.tree.locations.size = (returnTree raw).locations.size at readCapacity
  obtain ⟨_,held,_,_,_,originalFresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare
    (returnTree raw) raw.output.global raw.output.frame call.returnId room runtime
  have fresh : GeneralBorrowTagMap.Fresh literal.access.tree.tagMapping raw.output.global.nextPointerTag := by
    rw [readTags];exact originalFresh
  have currentRoom : literal.access.tree.nodes.size+1 ≤ 4294967295 := by rw [readNodes];exact nodeRoom
  have nodeAt : literal.access.tree.nodes.get raw.returnPointer.grant = some parentNode := by rw [readNodes];exact parentAt
  have bounds : (UInt64.ofNat call.returnOffset).toNat+1 ≤ literal.access.tree.locations.size.bytes.toNat := by
    rw [readCapacity];exact (endpoints input frame raw positive).2.2.2.2.1
  have own : literal.child.tree.indexOfTag raw.output.global.nextPointerTag = some borrowed.child := by
    simpa only [outputEq,literal,CurrentCallTypedFnEntry.literal] using borrowed.childLookup
  have tagBound : raw.output.global.nextPointerTag.value.toNat < literal.global.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value raw.output.global.nextPointerTag room
    change raw.output.global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag raw.output.global.nextPointerTag room).value.toNat
    omega
  have heldTag : literal.global.protectedTags.contains raw.output.global.nextPointerTag = true := by
    change (registered raw.output.global raw.output.frame call.returnId room).1.protectedTags.contains raw.output.global.nextPointerTag = true
    unfold ProtectedTags.contains
    rw [held]
    rfl
  cases prov : raw.returnPointer.value.provenance with
  | concrete id tag =>
    have tagged : literal.access.tree.indexOfTag tag = some raw.returnPointer.grant := by
      have tagEq : tag = parentNode.tag := by simpa [prov] using provenance
      rw [tagEq]
      exact (readComplete.2.2.2.2.1 raw.returnPointer.grant parentNode nodeAt).1
    obtain ⟨child,lookup,⟨node,found,nodeTag,_⟩,_,_⟩ := GeneralBorrowProtectedChildMetadata.construct literal.access.tree literal.global
      readRuntime tag raw.output.global.nextPointerTag raw.returnPointer.grant parentNode tagged nodeAt fresh currentRoom
      (UInt64.ofNat call.returnOffset) 1 (by decide) bounds
    have lookup' : literal.child.tree.indexOfTag raw.output.global.nextPointerTag = some child := by
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshMetadataChildMutableSlot.result,
        GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using lookup
    have same : child = borrowed.child := Option.some.inj (lookup'.symm.trans own)
    subst child
    refine ⟨node,?_,?_⟩
    · rw [outputEq]
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshMetadataChildMutableSlot.result,
        GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using found
    · rw [borrowed.tag]
      exact nodeTag
  | wildcard =>
    obtain ⟨_,_,_,_,child,lookup,_,⟨node,found,nodeTag,_,_⟩,_⟩ := GeneralBorrowWildcardConstructorRuntime.protected_mutable
      literal.access.tree literal.global readRuntime raw.output.global.nextPointerTag fresh currentRoom tagBound heldTag
      (UInt64.ofNat call.returnOffset) 1 (by decide) bounds
    have lookup' : literal.child.tree.indexOfTag raw.output.global.nextPointerTag = some child := by
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using lookup
    have same : child = borrowed.child := Option.some.inj (lookup'.symm.trans own)
    subst child
    refine ⟨node,?_,?_⟩
    · rw [outputEq]
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using found
    · rw [borrowed.tag]
      exact nodeTag

/-- Plain-memory compatibility with this selected profile's absent sync host.
The FIRST matching extras row is used. Arbitrary metadata outside the requested
window and in unrelated allocations remains permitted. -/
def WindowReady (before : Before) (id : AllocId) (offset length : Nat) : Prop :=
  ∃ sync : Array (Size × MemoryExtras.Entry Unit),
    before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,sync⟩) ∧
    ∀ row ∈ sync, row.1.bytes.toNat < offset ∨ offset+length ≤ row.1.bytes.toNat

/-- Execution representation for the selected plain-memory profile, separate
from Proposed/Freeze entitlements. A zero source needs no source extras row.
Same-allocation roles refer to the SAME actual first-match row by equality of
find? results; no distinct-allocation or globally empty-registry condition is
imposed. Ordinary ownership does not certify host metadata compatibility. -/
structure ProfileMemoryReadiness (before : Before) (call : CallLoans) : Prop where
  source : 0 < call.length → WindowReady before call.sourceId call.sourceOffset call.length
  bool : WindowReady before call.returnId call.returnOffset 1

theorem WindowReady.subrange {before id offset length}
    (ready : WindowReady before id offset length) (start count : Nat)
    (lower : offset ≤ start) (upper : start+count ≤ offset+length) : WindowReady before id start count := by
  obtain ⟨sync,present,outside⟩ := ready
  refine ⟨sync,present,?_⟩
  intro row member
  have original := outside row member
  omega

theorem WindowReady.transport {before after id offset length}
    (ready : WindowReady before id offset length)
    (extras : after.user.payload.payload.user.runtime.extras = before.user.payload.payload.user.runtime.extras) :
    WindowReady after id offset length := by
  obtain ⟨sync,present,outside⟩ := ready
  exact ⟨sync,by rw [extras];exact present,outside⟩

theorem ProfileMemoryReadiness.transport {before after call}
    (ready : ProfileMemoryReadiness before call)
    (extras : after.user.payload.payload.user.runtime.extras = before.user.payload.payload.user.runtime.extras) :
    ProfileMemoryReadiness after call :=
  ⟨fun positive => (ready.source positive).transport extras,ready.bool.transport extras⟩

/-- Actual push identity/relevance updates preserve the original profile row. -/
theorem ProfileMemoryReadiness.prepared {before call}
    (ready : ProfileMemoryReadiness before call) (frames : Array CompilerFrameContext.ActualFrame) :
    ProfileMemoryReadiness (CurrentCallPush.preparedMachine before frames) call := by
  constructor
  · intro positive
    obtain ⟨sync,present,outside⟩ := ready.source positive
    exact ⟨sync,present,outside⟩
  · obtain ⟨sync,present,outside⟩ := ready.bool
    exact ⟨sync,present,outside⟩

/-- Internal physical write leaf preserves the actual extras lookup and
synchronization-host boundary. The enclosing theorem must bind these raw
representation fields to the original machine; no successful access is assumed. -/
theorem write_uninit_concrete (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (state : RootState) (place : MPlaceTy Provenance)
    (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow state.machine place)
    (tracker : MachineHooks.BorrowState) (enabled : state.machine.borrowTracker = some tracker)
    (tag : BorTag) (concrete : physical.pointer.provenance = .concrete physical.id tag)
    (ghost : state.machine.user.payload.ghost = false)
    (race : state.machine.dataRace = none) (backend : state.machine.user.payload.payload.user.backend = .none)
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : state.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == physical.id) =
      some (physical.id,⟨none,sync⟩))
    (outside : ∀ row ∈ sync, row.1.bytes.toNat < physical.offset.toNat ∨ physical.offset.toNat+1 ≤ row.1.bytes.toNat)
    (completed : (physical.entry.allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed) :
    let written := physical.entry.allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    ∃ updated, (config options remaining span).retag.writeUninit place state =
      .ok () {state with machine := {state.machine with memory :=
        {state.machine.memory with live := ((state.machine.memory.live.filter fun row => row.1 != physical.id).push
          (physical.id,{physical.entry with allocation := updated}))}}} ∧
      updated.extra = written.tree ∧ updated.byteSize = physical.entry.allocation.byteSize ∧
      updated.len = physical.entry.allocation.len ∧ updated.mutability = .Mut ∧
      Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1))
        (Size.ofBytes 8) (physical.entry.allocation.setExtra written.tree) = .ok () updated := by
  let contexts := DuplicatePrefixPhysicalContexts.canonical options remaining span
  let context := contexts.validationContext
  have present : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == physical.id) =
      some (physical.id,⟨none,sync⟩) := extras
  have syncDone := S04ReturnSyncOutside.sync_access_outside context.extras state.machine physical.id
    (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) true ⟨none,sync⟩ present outside
  have actual := S04ReturnExtrasAccess.source_write_access_exact context.prepared context.image
    context.maximum context.fuel context.globalHooks context.pointers context.extras state.machine tracker
    physical.entry.allocation.extra physical.id (.concrete tag) (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1))
    sync race backend enabled present
  have access : PlaceMachine.memoryAccess context.access true ⟨state.machine,none⟩ physical.entry.allocation.extra
      physical.id (S04ReturnBorrowBridge.extra physical.pointer.provenance) (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) =
      ⟨⟨state.machine,none⟩,(physical.entry.allocation.extra.performBorrowAccessRange (.concrete tag)
        (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write tracker.global.protectedTags .VisitChildrenOfAccessed).tree,.ok ()⟩ := by
    change PlaceMachine.memoryAccess context.access true _ _ _ _ _ = _ at actual
    dsimp only [allocRange] at actual syncDone ⊢
    simpa only [completed,syncDone,concrete,S04ReturnBorrowBridge.extra,ite_true] using actual
  have resolved : context.access.resolvePointer state.machine.memory
      physical.pointer.withOptionalProvenance (Int.ofNat (1 : UInt64).toNat) state.machine =
      .ok (.ok ⟨physical.id,Size.ofBytes physical.offset,S04ReturnBorrowBridge.extra physical.pointer.provenance⟩) state.machine := by
    have off : physical.pointer.offset = Size.ofBytes (physical.base+physical.offset) := by
      cases h : physical.pointer.offset
      simpa [h,Size.ofBytes] using congrArg Size.ofBytes physical.pointerAddress
    rw [show context.access.resolvePointer = TypedMemoryProviders.resolvePointer context.pointers from rfl]
    have res := MemoryCopyBridge.typed_resolve_cached context.pointers state.machine.memory state.machine
      physical.id tag physical.base physical.offset (Int.ofNat (1 : UInt64).toNat) contexts.validationWidth
      (by decide) (by decide) physical.cachedBase
    simpa only [Pointer.withOptionalProvenance,concrete,off,Pointer.new,S04ReturnBorrowBridge.extra] using res
  have accessEq := contexts.accessEq
  rw [←accessEq] at access resolved
  exact CandidateCurrentBoolUninitWrite.configured options remaining span ctx state place physical _ ghost access resolved

def writeResult {before tracker frame argument len place call data}
    {raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data}
    (borrowed : Borrowed raw) : BorrowTree.BorrowTreeAccessResult :=
  borrowed.output.child.tree.performBorrowAccessRange (.concrete borrowed.output.tag)
    (Size.ofBytes (UInt64.ofNat call.returnOffset)) (Size.ofBytes 1) .Write borrowed.output.global.protectedTags .VisitChildrenOfAccessed

structure Written {before tracker frame argument len place call data}
    {raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data}
    (borrowed : Borrowed raw) : Prop where
  completed : (writeResult borrowed).status = .Completed
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts (writeResult borrowed).tree borrowed.output.global
  completes : Completes (writeResult borrowed).tree
    (S05ConcreteProtectedChildCompletion.extend (returnCompletion raw) borrowed.child raw.returnPointer.grant)
  nodes : (writeResult borrowed).tree.nodes = borrowed.output.child.tree.nodes
  capacity : (writeResult borrowed).tree.locations.size = borrowed.output.child.tree.locations.size
  sourceOwned :
    let tree := if call.sourceId = call.returnId then (writeResult borrowed).tree else raw.output.child.tree
    let completion := if call.sourceId = call.returnId then
      S05ConcreteProtectedChildCompletion.extend (returnCompletion raw) borrowed.child raw.returnPointer.grant
      else S05ConcreteProtectedChildCompletion.extend raw.sourcePrecise.completion raw.child raw.sourcePointer.grant
    GeneralRangeMapOrigins.OwnedOn
      (Authority tree completion borrowed.output.global.protectedTags raw.child)
      (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) tree.locations

/-- The fresh concrete Bool child Write completes and preserves the whole
source window. Its old parent authority is intentionally not claimed while
this strong protected child is live. -/
theorem written {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState) (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (positive : 0 < len.toNat) (borrowed : Borrowed raw) : Written borrowed := by
  obtain ⟨node,nodeAt,nodeTag⟩ := borrowed_node input frame raw positive borrowed
  have bounds : (UInt64.ofNat call.returnOffset).toNat+1 ≤ borrowed.output.child.tree.locations.size.bytes.toNat := by
    rw [borrowed.metadata.capacity]
    exact (endpoints input frame raw positive).2.2.2.2.1
  have short : borrowed.output.child.tree.nodes.size < 65536 := by
    have budget := (return_budget input frame raw).2.2
    have growth := borrowed.metadata.growth
    omega
  have empty : GeneralRangeMapOrigins.OwnedOn
      (Authority borrowed.output.child.tree
        (S05ConcreteProtectedChildCompletion.extend (returnCompletion raw) borrowed.child raw.returnPointer.grant)
        borrowed.output.global.protectedTags borrowed.child) 0 0 borrowed.output.child.tree.locations := by
    intro cursor valid positive
    change (0 : UInt64).toNat < (0 : UInt64).toNat at positive
    omega
  obtain ⟨completed,runtime,complete,nodes,capacity,_⟩ := write_range borrowed.output.child.tree borrowed.output.global
    (S05ConcreteProtectedChildCompletion.extend (returnCompletion raw) borrowed.child raw.returnPointer.grant)
    borrowed.runtime borrowed.completes borrowed.metadata.order borrowed.child node nodeAt
    (UInt64.ofNat call.returnOffset) bounds short borrowed.boolOwned borrowed.child 0 0
    (by intro point lower upper;omega) empty
  rw [nodeTag] at completed runtime complete nodes capacity
  refine ⟨completed,runtime,complete,nodes,capacity,?_⟩
  have sourceOwned := borrowed.sourceOwned
  by_cases same : call.sourceId = call.returnId
  · simp only [same,ite_true] at sourceOwned ⊢
    have disjoint := (endpoints input frame raw positive).2.2.2.2.2 same
    have framed := GeneralBorrowRangeOutsideOwned.owned
      (Authority borrowed.output.child.tree
        (S05ConcreteProtectedChildCompletion.extend (returnCompletion raw) borrowed.child raw.returnPointer.grant)
        borrowed.output.global.protectedTags raw.child)
      borrowed.output.child.tree (.concrete borrowed.output.tag) (Size.ofBytes (UInt64.ofNat call.returnOffset)) (Size.ofBytes 1)
      .Write borrowed.output.global.protectedTags .VisitChildrenOfAccessed borrowed.runtime.formed.well bounds
      (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) disjoint sourceOwned
    intro cursor valid positive start stop index current present
    exact framed cursor valid positive start stop index current (by rw [←nodes];exact present)
  · simpa only [same,ite_false] using sourceOwned

/-- Actual uninit changes initialization/provenance metadata, preserving bytes. -/
theorem uninit_snapshot {Prov Extra : Type} [DecidableEq Prov]
    (allocation updated : Allocation Prov Extra) (range : AllocRange) (pointerSize : Size)
    (actual : Allocation.writeUninit range pointerSize allocation = .ok () updated) :
    AllocationCopy.snapshot updated = AllocationCopy.snapshot allocation := by
  cases allocation
  unfold Allocation.writeUninit at actual
  unfold_internal_at ".Allocation.setInitialization" at actual
  simp only [Id.run,bind,pure,Except.mapError,Bind.bind,Pure.pure,Except.bind,Except.pure] at actual
  repeat' first
    | split at *
    | contradiction
  all_goals try simp_all only [EStateM.Result.ok.injEq,Except.ok.injEq]
  all_goals cases actual <;> subst_vars <;> rfl

/-- Physical source initialization is framed by the SAME actual uninit
mutation. It covers every disjoint initialized interval, not a one-byte source. -/
theorem initialized_frame {before : Before} {place : MPlaceTy Provenance}
    (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow before place)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree)
    (mutation : Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
      (physical.entry.allocation.setExtra tree) = .ok () updated)
    (start finish : Size)
    (initialized : InitMaskCopy.InitializedOn physical.entry.allocation.initializationMask start finish)
    (positive : start.bytes.toNat < finish.bytes.toNat)
    (sourceBounds : finish.bytes.toNat ≤ physical.entry.allocation.initializationMask.len.bytes.toNat)
    (disjoint : finish.bytes.toNat ≤ physical.offset.toNat ∨ (physical.offset+1).toNat ≤ start.bytes.toNat) :
    InitMaskCopy.InitializedOn updated.initializationMask start finish := by
  obtain ⟨expected,actual,maskEq,_,_,_,_,_,_,_⟩ := S02SameDestinationUninitInitializedMutation.uninit
    (physical.entry.allocation.setExtra tree) physical.capacity physical.offset physical.bytes physical.size physical.mutable
    physical.maskValid physical.maskLength physical.provenanceMap physical.bounds
  have equal : expected = updated := (EStateM.Result.ok.inj (actual.symm.trans mutation)).2
  subst expected
  have endNat : (physical.offset+1).toNat = physical.offset.toNat+1 := by
    rw [UInt64.toNat_add]
    change (physical.offset.toNat+1)%2^64 = physical.offset.toNat+1
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt physical.bounds physical.capacity.toNat_lt)
  have endpoint : (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)).endExclusive =
      .ok (Size.ofBytes (physical.offset+1)) := DuplicatePrefix.source_end (Size.ofBytes physical.offset) 1
        (Nat.lt_of_le_of_lt physical.bounds physical.capacity.toNat_lt)
  obtain ⟨mask,setEq,_,_,frame⟩ := S02SameDestinationUninitInitializedBits.one_byte_frame
    physical.entry.allocation.initializationMask start finish (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1))
    (Size.ofBytes (physical.offset+1)) physical.maskValid initialized positive sourceBounds endpoint endNat
    (by rw [physical.maskLength];simpa only [Size.ofBytes,endNat] using physical.bounds) disjoint
  have same : mask = updated.initializationMask := Except.ok.inj (setEq.symm.trans maskEq)
  rw [same] at frame
  exact frame

/-- In the shared-allocation case, the entire original initialized source
interval survives the actual Bool uninit mutation. The physical entry is bound
to the real post-source memory lookup, not supplied as a new source packet. -/
theorem same_source_initialized {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    {ctx : ActualReferenceContext.Context options remaining span}
    {frames : Array CompilerFrameContext.ActualFrame} {frame : CompilerFrameContext.ActualFrame} {borrowFrame : FrameState}
    (source : CurrentCallReferenceEntry.ViewedOutcome options remaining span ctx before tracker frames frame borrowFrame argument len place call data .FnEntry true)
    (positive : 0 < len.toNat)
    (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow (CurrentCallBoolWindow.after source) place)
    (idEq : physical.id = call.returnId) (offsetEq : physical.offset = UInt64.ofNat call.returnOffset)
    (same : call.sourceId = call.returnId) (tree : BorrowTree) (updated : Allocation Provenance BorrowTree)
    (mutation : Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
      (physical.entry.allocation.setExtra tree) = .ok () updated) :
    InitMaskCopy.InitializedOn updated.initializationMask (Size.ofBytes (UInt64.ofNat call.sourceOffset))
      (Size.ofBytes (UInt64.ofNat call.sourceOffset+len)) := by
  let raw := source.base.raw
  have physicalLive : (CurrentCallBoolWindow.after source).memory.live.find? (fun row => row.1 == call.sourceId) =
      some (call.sourceId,physical.entry) := by simpa only [idEq,←same] using physical.live
  have sourceLive : (CurrentCallBoolWindow.after source).memory.live.find? (fun row => row.1 == call.sourceId) =
      some (call.sourceId,{source.base.entry with allocation := source.base.entry.allocation.setExtra raw.output.child.tree}) := source.sourceInstalled
  have entryEq := (Prod.mk.inj (Option.some.inj (physicalLive.symm.trans sourceLive))).2
  have maskEq : physical.entry.allocation.initializationMask = raw.sourceAllocation.initializationMask := by
    rw [entryEq]
    change source.base.entry.allocation.initializationMask = raw.sourceAllocation.initializationMask
    rw [source.base.sourceAllocation]
  have sourcePhysical : OrdinaryPhysicalValidity.MutU8Slice raw.sourceAllocation (UInt64.ofNat call.sourceOffset) len := by
    rcases input.actual.sourceValue with ⟨zero,_⟩ | ⟨_,allocation,present,physical⟩
    · simp [zero] at positive
    · have sameAllocation := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList input.machine.worldIds
        call.sourceId allocation raw.sourceAllocation present raw.sourcePresent
      rw [sameAllocation] at physical
      exact physical
  obtain ⟨sourceOffsetEq,returnOffsetEq,sourceSum,returnSum,_,disjoint⟩ := endpoints input borrowFrame raw positive
  have initialization : InitMaskCopy.InitializedOn physical.entry.allocation.initializationMask
      (Size.ofBytes (UInt64.ofNat call.sourceOffset)) (Size.ofBytes (UInt64.ofNat call.sourceOffset+len)) := by
    rw [maskEq]
    exact sourcePhysical.slice_storage.initialized
  have bound : (UInt64.ofNat call.sourceOffset+len).toNat ≤ physical.entry.allocation.initializationMask.len.bytes.toNat := by
    rw [maskEq,sourcePhysical.storage.maskLength]
    rw [sourceSum]
    have containment := sourcePhysical.contained
    rw [sourceOffsetEq] at containment
    exact containment
  have separate : (UInt64.ofNat call.sourceOffset+len).toNat ≤ physical.offset.toNat ∨
      (physical.offset+1).toNat ≤ (UInt64.ofNat call.sourceOffset).toNat := by
    rw [offsetEq,returnOffsetEq,returnSum,sourceSum,sourceOffsetEq]
    apply Classical.byContradiction
    intro bad
    have lower : (UInt64.ofNat call.sourceOffset).toNat ≤ (UInt64.ofNat call.returnOffset).toNat := by omega
    have upper : (UInt64.ofNat call.returnOffset).toNat < (UInt64.ofNat call.sourceOffset+len).toNat := by omega
    have conflict := disjoint same (UInt64.ofNat call.returnOffset) lower upper
    rw [returnOffsetEq,returnSum] at conflict
    omega
  exact initialized_frame physical tree updated mutation _ _ initialization
    (by simpa only [Size.ofBytes,sourceOffsetEq,sourceSum] using (show call.sourceOffset < call.sourceOffset+len.toNat by omega))
    bound separate

/-- The actual two-copy result supplies the callee protector frame; it is not
an additional prepared-frame admission condition. Span/local changes retain it. -/
theorem argument_frame {options remaining span ctx before tracker frames frame borrowFrame argument len place call data}
    (source : CurrentCallReferenceEntry.ViewedOutcome options remaining span ctx before tracker frames frame borrowFrame
      argument len place call data .FnEntry true)
    (valid : 1 < frame.locals.size) (firstDone : RootFrameData.RootFrame)
    (frameEq : firstDone.frame = CurrentCallReferenceEntry.writtenFrame source 1 valid) (count : UInt64) :
    (RootArgumentsTwo.result firstDone count).frame.extra.borrowTracker = some source.base.raw.output.frame := by
  change firstDone.frame.extra.borrowTracker = _
  rw [frameEq]
  exact source.base.outputFrame

/-- Full actual Bool protectArgument after argument copying. The temporary
retagged place is discarded; its child/protector stay live until pop. The
original returnPlace is retained.
Selected-profile metadata readiness is explicit execution representation. -/
theorem protect_after_source
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (retagCtx : ActualRetagContext.Context options (remaining+1) span)
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (readiness : ProfileMemoryReadiness before call)
    (frames : Array CompilerFrameContext.ActualFrame) (initialFrame : CompilerFrameContext.ActualFrame)
    (initialBorrow : FrameState)
    (source : CurrentCallReferenceEntry.ViewedOutcome options remaining span ctx before tracker frames initialFrame initialBorrow
      argument len place call data .FnEntry true)
    (frame : CompilerFrameContext.ActualFrame)
    (frameBorrow : frame.extra.borrowTracker = some source.base.raw.output.frame)
    (positive : 0 < len.toNat) :
    ∃ borrowed : Borrowed source.base.raw, Written borrowed ∧
      ∃ physical : CandidateCurrentBoolUninitWrite.PhysicalWindow (CurrentCallBoolWindow.after source) place,
      ∃ room : source.base.raw.output.global.nextPointerTag.value < 18446744073709551615,
      ∃ updated : Allocation Provenance BorrowTree,
        physical.id = call.returnId ∧ physical.pointer = source.base.raw.returnPointer.value ∧ physical.offset = UInt64.ofNat call.returnOffset ∧
        let retagged := borrowedState frames frame source.base.raw.output.frame (CurrentCallBoolWindow.after source)
          ⟨source.base.raw.output.global,tracker.retagMode⟩ room physical.id physical.entry borrowed.output.child.tree
        let final := {retagged with machine := {retagged.machine with memory :=
          {retagged.machine.memory with live := ((retagged.machine.memory.live.filter fun row => row.1 != physical.id).push
            (physical.id,{{physical.entry with allocation := physical.entry.allocation.setExtra borrowed.output.child.tree} with allocation := updated}))}}}
        (ExecutionMachine.callHooks (config options (remaining+1) span) limits).protectArgument () place
          (Storage.withCurrent frames frame (CurrentCallBoolWindow.after source)) = .ok () final ∧
        updated.extra = (writeResult borrowed).tree ∧
        Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
          ((physical.entry.allocation.setExtra borrowed.output.child.tree).setExtra (writeResult borrowed).tree) = .ok () updated ∧
        AllocationCopy.snapshot updated = AllocationCopy.snapshot physical.entry.allocation ∧
        ProfileMemoryReadiness final.machine call ∧
        CandidateCallBindings.WindowBinding final.machine
          (CurrentCallTypedFnEntry.changedPointer source.base.raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag)
          call.sourceId call.sourceOffset len.toNat ∧
        (call.sourceId = call.returnId → InitMaskCopy.InitializedOn updated.initializationMask
          (Size.ofBytes (UInt64.ofNat call.sourceOffset)) (Size.ofBytes (UInt64.ofNat call.sourceOffset+len))) ∧
        (registeredFrame frame source.base.raw.output.frame physical.id source.base.raw.output.global.nextPointerTag).returnPlace = frame.returnPlace := by
  let raw := source.base.raw
  let machine := CurrentCallBoolWindow.after source
  let currentTracker : MachineHooks.BorrowState := ⟨raw.output.global,tracker.retagMode⟩
  obtain ⟨borrowed,physical,room,idEq,pointerEq,offsetEq,treeEq,retag⟩ := retag_after_source options limits remaining span ctx retagCtx
    before tracker argument len place call data input frames initialFrame initialBorrow source frame frameBorrow positive
  have wrote := written input initialBorrow raw positive borrowed
  let retagged := borrowedState frames frame raw.output.frame machine currentTracker room physical.id physical.entry borrowed.output.child.tree
  let childWindow := CurrentCallBoolWindow.protected_window physical frames frame raw.output.frame currentTracker room borrowed.output.child.tree
  have outputEq : borrowed.output = CurrentCallTypedFnEntry.literal (returnTree raw) raw.output.global raw.output.frame call.returnId room
      raw.returnPointer.value.provenance (UInt64.ofNat call.returnOffset) 1 := Except.ok.inj
    (borrowed.actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ room _ _ _))
  have enabled : retagged.machine.borrowTracker = some ⟨borrowed.output.global,tracker.retagMode⟩ := by
    rw [outputEq]
    rfl
  have ghost : retagged.machine.user.payload.ghost = false := rfl
  have race : retagged.machine.dataRace = none := input.machine.settings.noDataRace
  have backend : retagged.machine.user.payload.payload.user.backend = .none := input.machine.settings.noBackend
  obtain ⟨sync,extras,outside⟩ := readiness.bool
  have extraAt : retagged.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == childWindow.id) =
      some (childWindow.id,⟨none,sync⟩) := by
    change before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == physical.id) = some (physical.id,⟨none,sync⟩)
    simpa only [idEq] using extras
  have outside' : ∀ row ∈ sync, row.1.bytes.toNat < childWindow.offset.toNat ∨ childWindow.offset.toNat+1 ≤ row.1.bytes.toNat := by
    intro row member
    have offsetNat := (endpoints input initialBorrow raw positive).2.1
    have original := outside row member
    simpa only [childWindow,CurrentCallBoolWindow.protected_window,CurrentCallBoolWindow.retagged,
      CurrentCallBoolWindow.tree_only,offsetEq,offsetNat] using original
  have concrete : childWindow.pointer.provenance = .concrete childWindow.id raw.output.global.nextPointerTag := rfl
  have completed : (childWindow.entry.allocation.extra.performBorrowAccessRange (.concrete raw.output.global.nextPointerTag)
      (Size.ofBytes childWindow.offset) (Size.ofBytes 1) .Write borrowed.output.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    simpa only [childWindow,CurrentCallBoolWindow.protected_window,CurrentCallBoolWindow.retagged,CurrentCallBoolWindow.tree_only,
      Allocation.setExtra,Allocation.mapExtra,offsetEq,writeResult,borrowed.tag,raw] using wrote.completed
  obtain ⟨updated,write,extra,byteSizeEq,lengthEq,_,mutation⟩ := write_uninit_concrete options (remaining+1) span retagCtx retagged
    (TypedRetagGeneric.retaggedPlace place physical.id raw.output.global.nextPointerTag) childWindow
    ⟨borrowed.output.global,tracker.retagMode⟩ enabled raw.output.global.nextPointerTag concrete ghost race backend sync extraAt outside' completed
  let finalMachine : Before := {retagged.machine with memory :=
    {retagged.machine.memory with live := ((retagged.machine.memory.live.filter fun row => row.1 != physical.id).push
      (physical.id,{physical.entry with allocation := updated}))}}
  have retag' : TypedRetag.retagPlace (config options (remaining+1) span).retag limits.retag place MachineHooks.protectionPolicy
      (Storage.withCurrent frames frame machine) = .ok (TypedRetagGeneric.retaggedPlace place physical.id raw.output.global.nextPointerTag) retagged := by
    simpa only [idEq,retagged,machine,currentTracker,raw] using retag
  refine ⟨borrowed,wrote,physical,room,updated,idEq,pointerEq,offsetEq,?_,?_,?_,?_,?_,?_,?_,rfl⟩
  · change TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag limits.retag place (Storage.withCurrent frames frame machine) = _
    unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace
    simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,Storage.withCurrent,
      show machine.borrowTracker = some currentTracker from rfl,
      Option.isSome_some,ite_true]
    erw [retag']
    exact write
  · simpa only [childWindow,CurrentCallBoolWindow.protected_window,CurrentCallBoolWindow.retagged,CurrentCallBoolWindow.tree_only,
      Allocation.setExtra,Allocation.mapExtra,offsetEq,writeResult,borrowed.tag,raw] using extra
  · simpa only [childWindow,CurrentCallBoolWindow.protected_window,CurrentCallBoolWindow.retagged,CurrentCallBoolWindow.tree_only,
      Allocation.setExtra,Allocation.mapExtra,offsetEq,writeResult,borrowed.tag,raw] using mutation
  · have preserved := uninit_snapshot _ updated _ _ mutation
    exact preserved
  · exact readiness.transport rfl
  · apply CurrentCallBoolWindow.source_after_write options limits remaining span ctx before tracker argument len place call data
      input frames initialFrame initialBorrow source positive physical updated finalMachine lengthEq byteSizeEq rfl
    exact congrArg (fun memory => memory.live) (MemoryCopyBridge.live_update_twice machine.memory physical.id
      {physical.entry with allocation := physical.entry.allocation.setExtra borrowed.output.child.tree}
      {physical.entry with allocation := updated})
  · intro same
    apply same_source_initialized input source positive physical idEq offsetEq same (writeResult borrowed).tree updated
    simpa only [childWindow,CurrentCallBoolWindow.protected_window,CurrentCallBoolWindow.retagged,CurrentCallBoolWindow.tree_only,
      Allocation.setExtra,Allocation.mapExtra,offsetEq,writeResult,borrowed.tag,raw] using mutation

end
end DuplicatePrefix.CurrentCallBoolProtection

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallBoolProtection." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved actual current Bool protection dependency {dependency}"
