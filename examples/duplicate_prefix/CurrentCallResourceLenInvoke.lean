import duplicate_prefix.CurrentCallResourceSharedInvoke
import duplicate_prefix.CurrentCallLenReadBody
import duplicate_prefix.RelevanceCurrent

namespace DuplicatePrefix.CurrentCallResourceLenInvoke
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallResourceEntryBody GeneralBorrowFnEntryRegistration GeneralBorrowRawSharedExpression
open GeneralBorrowExposedNonleafPrimaryPath GeneralRangeMapOrigins
open CanonicalConfigFacts ActualReferenceContext LenUncachedFrontend GeneralBorrowForestMixedLenBeforeReturn
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

private theorem path_frame (before after : BorrowTree)
    (old : ∀ index node,before.nodes.get index=some node → ∃ next,after.nodes.get index=some next ∧ next.parent=node.parent)
    {root target : UniIndex} (path : Path before root target) : Path after root target := by
  induction path with
  | refl node present =>
    obtain ⟨next,found,_⟩ := old _ node present
    exact .refl _ next found
  | @step predecessor target earlier node present edge ih =>
    obtain ⟨next,found,same⟩ := old target node present
    exact .step ih next found (same.trans edge)

private theorem written_slot (frame : CompilerFrameContext.ActualFrame) (localId : MIR.LocalId)
    (layout : LocalLayout) (valid : localId<frame.locals.size) (value : Immediate Provenance) :
    (ActualLocalCopy.written frame localId layout valid value).locals[localId]?=
      some ⟨.live (.immediate value),some layout⟩ := by
  simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]

private theorem written_other (frame : CompilerFrameContext.ActualFrame) (source dest : MIR.LocalId)
    (layout : LocalLayout) (valid : dest<frame.locals.size) (value : Immediate Provenance) (different : source≠dest) :
    (ActualLocalCopy.written frame dest layout valid value).locals[source]?=frame.locals[source]? := by
  simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Ne.symm different]

private theorem local_cell (locals : Array (LocalState Provenance LocalLayout)) (localId : MIR.LocalId)
    (valid : localId<locals.size) (value : Immediate Provenance) (layout : LocalLayout)
    (stored : locals[localId]?=some ⟨.live (.immediate value),some layout⟩) :
    locals[localId].value=.live (.immediate value) ∧ locals[localId].layout=some layout := by
  have same : locals[localId]=⟨.live (.immediate value),some layout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans stored)
  rw [same]
  exact ⟨rfl,rfl⟩

private theorem afterPush_types (machine : Before) (size : Nat) (newRank oldRank : UInt8) :
    (GenericPushRelevance.afterPush machine size newRank oldRank).user.payload.payload.user.types=
      machine.user.payload.payload.user.types := by
  unfold GenericPushRelevance.afterPush
  split <;> rfl

theorem stage_geometry {before tracker data owner id offset length}
    (Q : UniformWindow before tracker data owner id offset length .mut)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra tracker.global)
    (distinct : Q.allocation.extra.roots.toList.Nodup)
    (tag : BorTag) (concrete : Q.pointer.value.provenance=.concrete id tag)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64)
    (stage : CurrentCallResourceSharedResources.Stage Q tag start amount room)
    (nodeRoom : Q.allocation.extra.nodes.size+1≤4294967295) (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤Q.allocation.extra.locations.size.bytes.toNat) :
    let actual := child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed
    ∃ rootNode readerNode,
      actual.tree.roots.toList.Nodup ∧
      actual.tree.roots[stage.preparation.geometry.selectedPosition]?=some stage.preparation.geometry.selectedRoot ∧
      actual.tree.nodes.get stage.preparation.geometry.selectedRoot=some rootNode ∧
      actual.tree.nodes.get stage.reader=some readerNode ∧ readerNode.tag=tracker.global.nextPointerTag ∧
      Path actual.tree stage.preparation.geometry.selectedRoot Q.pointer.grant ∧
      Path actual.tree stage.preparation.geometry.selectedRoot stage.reader ∧
      (∀ root,actual.tree.roots[0]?=some root → Below
        (S05ConcreteProtectedChildCompletion.extend Q.precise.completion stage.reader Q.pointer.grant) root Q.pointer.grant) := by
  let after := read Q.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed
  let actual := child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed
  let P := stage.preparation
  have high := GeneralBorrowForestTagHighWater.complete Q.allocation.extra _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,nodeFresh,_⟩ := GenericFunctionTagFormation.fresh_above Q.allocation.extra _ _ tracker.global.nextPointerTag high (Nat.le_refl _)
  have freshAfter : GeneralBorrowTagMap.Fresh after.tree.tagMapping tracker.global.nextPointerTag := by rw [P.tags];exact fresh
  obtain ⟨parent,parentAt,_,binding⟩ := Q.binding
  rw [concrete] at binding
  have parentAfter : after.tree.nodeAt Q.pointer.grant=some parent := by change after.tree.nodes.get _=_;rw [P.nodes];exact parentAt
  have tagged : after.tree.indexOfTag tag=some Q.pointer.grant := by rw [binding.2];exact P.runtime.formed.allocator.nodeTags _ _ parentAfter
  have boundsAfter : start.toNat+amount.toNat≤after.tree.locations.size.bytes.toNat := by rw [P.capacity];exact bounds
  have roomAfter : after.tree.nodes.size+1≤4294967295 := by change after.tree.nodes.data.size+1≤_;rw [P.nodes];exact nodeRoom
  obtain ⟨r,lookup,⟨readerNode,readerAt,readerTag,readerParent,_⟩,old⟩ := GeneralBorrowSharedChildGraph.construct after.tree (advanced tracker.global room) P.runtime
    tag tracker.global.nextPointerTag Q.pointer.grant parent tagged parentAfter freshAfter roomAfter false start amount nonzero boundsAfter
  have same : r=stage.reader := Option.some.inj (lookup.symm.trans stage.lookup)
  subst r
  obtain ⟨other,otherLookup,metadata⟩ := GeneralBorrowSharedReadMetadata.construct after.tree (advanced tracker.global room) P.runtime
    tag tracker.global.nextPointerTag Q.pointer.grant parent tagged parentAfter freshAfter roomAfter false start amount nonzero boundsAfter
  have roots : actual.tree.roots=Q.allocation.extra.roots := metadata.roots.trans P.roots
  have sourceRead : Path after.tree P.geometry.selectedRoot Q.pointer.grant :=
    GeneralBorrowPrimaryWitnessVisibility.path_nodes P.nodes.symm P.geometry.sourcePath
  have sourcePath : Path actual.tree P.geometry.selectedRoot Q.pointer.grant := path_frame after.tree actual.tree
    (fun index node present => by obtain ⟨next,found,_,same,_⟩ := old index node present;exact ⟨next,found,same⟩) sourceRead
  have rootAtRead : after.tree.nodes.get P.geometry.selectedRoot=some P.geometry.selectedNode := by rw [P.nodes];exact P.geometry.selectedAt
  obtain ⟨rootNode,rootAt,_,_,_⟩ := old P.geometry.selectedRoot P.geometry.selectedNode rootAtRead
  have vacant : after.tree.nodes.get stage.reader=none := by
    cases original : after.tree.nodes.get stage.reader with
    | none => rfl
    | some oldNode =>
      obtain ⟨next,nextAt,nextTag,_,_⟩ := old stage.reader oldNode original
      have sameNode : next=readerNode := Option.some.inj (nextAt.symm.trans readerAt)
      have tagEq : oldNode.tag=tracker.global.nextPointerTag := nextTag.symm.trans ((congrArg TreeNode.tag sameNode).trans readerTag)
      have originalAt : Q.allocation.extra.nodes.get stage.reader=some oldNode := by rw [←P.nodes];exact original
      exact False.elim (nodeFresh (stage.reader,oldNode)
        (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get Q.allocation.extra.nodes stage.reader oldNode).mpr originalAt)) tagEq)
  refine ⟨rootNode,readerNode,?_,?_,rootAt,readerAt,readerTag,sourcePath,.step sourcePath readerNode readerAt readerParent,?_⟩
  · rw [roots];exact distinct
  · rw [roots];exact P.geometry.selectedSlot
  · intro root slot
    have originalSlot : Q.allocation.extra.roots[0]?=some root := by rw [←roots];exact slot
    have rootEq : root=allocationRoot := Option.some.inj (originalSlot.symm.trans Q.issued.capability.rootSlot)
    rw [rootEq]
    exact CurrentCallResourceChild.old_ancestry after.tree Q.precise.completion P.parents stage.reader Q.pointer.grant vacant Q.root_below

variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    (out : Output limits C count) (ready : CurrentCallResourceBodyReadiness.Ready C)

private theorem shared_size (frame : CompilerFrameContext.ActualFrame)
    (shape : GenericFunctionEntryPrefix.Shape (CurrentCallResourceEntry.finishedFrame out) frame count) (base : UInt64) :
    (CurrentCallResourceSharedStage.afterFrame out frame (by rw [shape.size];decide) base).locals.size=25 := by
  simpa only [CurrentCallResourceSharedStage.afterFrame,CopyHelperSteps.advance,ActualLocalCopy.written,
    LocalPlaces.cachePlaceLayout,Array.size_set] using shape.size

def sharedFrame (frame : CompilerFrameContext.ActualFrame)
    (shape : GenericFunctionEntryPrefix.Shape (CurrentCallResourceEntry.finishedFrame out) frame count) (base : UInt64) :=
  CurrentCallResourceSharedStage.afterFrame out frame (by rw [shape.size];decide) base

def held : MachineHooks.BorrowState := ReferenceBorrowDriver.allocatedTracker ⟨out.boolOutput.global,tracker.retagMode⟩
  (CurrentCallResourceBodyReadiness.current_room out ready)

def entry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
  {(CurrentCallResourceSourceFinal.entry out) with allocation := (CurrentCallResourceSourceFinal.entry out).allocation.setExtra (CurrentCallResourceSharedStage.tree out)}

theorem helper_room : (held out ready).global.nextPointerTag.value<18446744073709551615 := by
  have room:=CurrentCallResourceBodyReadiness.current_room out ready
  have successor:=GenericFunctionEntryNumerics.successor_value out.boolOutput.global.nextPointerTag room
  apply UInt64.lt_iff_toNat_lt.mpr
  change (TypedRetagEmpty.successorTag out.boolOutput.global.nextPointerTag room).value.toNat<18446744073709551615
  rw [successor]
  have budget:=CurrentCallResourceBodyReadiness.current_tags out ready
  omega

def borrowedTree := CurrentCallLenArgumentCopy.finalTree (CurrentCallResourceSharedStage.tree out) (held out ready)
  out.boolOutput.global.nextPointerTag (UInt64.ofNat offset) len

/-- Output evidence from the actual helper call/body. Its sole trace starts
at the SAME completed shared-reference statement, before any helper call. -/
structure Returned (frame : CompilerFrameContext.ActualFrame)
    (shape : GenericFunctionEntryPrefix.Shape (CurrentCallResourceEntry.finishedFrame out) frame count) (base : UInt64) where
  helper : CompilerFrameContext.ActualFrame
  machine : Before
  trace : SuccessfulTrace.Trace (config options (remaining+1) span) limits
    (Storage.withCurrent #[] (sharedFrame out frame shape base) (CurrentCallResourceSharedStage.afterMachine out ready))
    (Storage.withCurrent #[(cachedCaller (sharedFrame out frame shape base) (by rw [sharedFrame,shared_size out frame shape base];decide))] helper machine)
  location : helper.location=.mir ⟨1,1⟩
  returned : helper.locals[0]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩
  protector : helper.extra.borrowTracker=some (({} : FrameState).addProtector id (held out ready).global.nextPointerTag)
  clocks : helper.extra.dataRace=none
  destination : helper.returnPlace.toRuntimePlace=LocalPlaces.localRuntimePlace 0
    (cachedCaller (sharedFrame out frame shape base) (by rw [sharedFrame,shared_size out frame shape base];decide)) 11 RootCompilerFacts.usizeLayout
  continuation : helper.returnContinuation=.goto (some 3) .Continue
  varargs : helper.vaList=#[]
  memory : machine.memory=RetagEntry.updatedMemory (CurrentCallResourceSharedStage.afterMachine out ready).memory id (entry out) (borrowedTree out ready)
  tracked : machine.borrowTracker=some (TypedBorrowSteps.registeredTracker
    (ReferenceBorrowDriver.allocatedTracker (held out ready) (helper_room out ready)) (held out ready).global.nextPointerTag)
  ghost : machine.user.payload.ghost=false
  shallow : machine.user.payload.validation=.Shallow
  race : machine.dataRace=none
  addresses : machine.user.addresses=(CurrentCallResourceSharedStage.afterMachine out ready).user.addresses
  types : machine.user.payload.payload.user.types=(CurrentCallResourceSharedStage.afterMachine out ready).user.payload.payload.user.types
  extras : machine.user.payload.payload.user.runtime.extras=(CurrentCallResourceSharedStage.afterMachine out ready).user.payload.payload.user.runtime.extras
  facts : ReturnFacts options remaining span helper machine len
    (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id (held out ready).global.nextPointerTag) (Size.ofBytes (base+UInt64.ofNat offset))) len SharedReferenceMetadata.sharedLayout).imm
  cache : RootCache #[] machine

/-- The correlated Default-shared stage supplies the narrow resources; all
physical, metadata and control inputs to the existing Len body are derived. -/
theorem before_return
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (budget : Nat) (dispatch : limits.callDispatch=budget+1)
    (frame : CompilerFrameContext.ActualFrame)
    (shape : GenericFunctionEntryPrefix.Shape (CurrentCallResourceEntry.finishedFrame out) frame count)
    {nextData nextOwner}
    (Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut)
    (pointer : Q.pointer=CurrentCallResourceSourceAfterBool.pointer out)
    (allocation : Q.allocation=(CurrentCallResourceSourceFinal.entry out).allocation)
    (stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len
      (CurrentCallResourceBodyReadiness.current_room out ready))
    (base : UInt64)
    (cached : (CurrentCallResourceSharedStage.machine out).user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (nonnull : base+UInt64.ofNat offset≠0) : Nonempty (Returned out ready frame shape base) := by
  let beforeMachine:=CurrentCallResourceSharedStage.afterMachine out ready
  let machine:=PtrMetadataReturn.accountedMachine options remaining span beforeMachine
  let current:=held out ready
  let rValue := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id out.boolOutput.global.nextPointerTag) (Size.ofBytes (base+UInt64.ofNat offset))) len SharedReferenceMetadata.sharedLayout).imm
  have callerSize : (sharedFrame out frame shape base).locals.size=25 := shared_size out frame shape base
  have sourceSlot : (sharedFrame out frame shape base).locals[12]?=some ⟨.live (.immediate rValue),some SharedReferenceMetadata.sharedLayout⟩ :=
    written_slot frame 12 SharedReferenceMetadata.sharedLayout (by rw [shape.size];decide) rValue
  have slot11 : (sharedFrame out frame shape base).locals[11]?=some ⟨.live (.immediate .uninit),none⟩ :=
    (written_other frame 11 12 SharedReferenceMetadata.sharedLayout (by rw [shape.size];decide) rValue (by decide)).trans shape.slot11
  have sourceBody : (sharedFrame out frame shape base).body=RootBody.reflected.body.body := shape.body.trans ((CurrentCallResourceEntryFacts.metadata out).1.trans root.body)
  have identity : (sharedFrame out frame shape base).bodyIdentity=RootBody.reflected.body.identity := shape.identity.trans ((CurrentCallResourceEntryFacts.metadata out).2.1.trans root.identity)
  have callee : (sharedFrame out frame shape base).functionInstance=RootBody.reflected.functionInstance := shape.callee.trans ((CurrentCallResourceEntryFacts.metadata out).2.2.1.trans root.callee)
  have noClocks : (sharedFrame out frame shape base).extra.dataRace=none := by
    change frame.extra.dataRace=none
    rw [shape.extra]
    exact (CurrentCallResourceEntryFacts.metadata out).2.2.2.2.2.2.1.trans root.noClocks
  have located : (sharedFrame out frame shape base).location=.mir ⟨2,12⟩ := rfl
  generalize callerEq : sharedFrame out frame shape base=caller at callerSize sourceSlot slot11 sourceBody identity callee noClocks located
  have v11 : 11<caller.locals.size := by rw [callerSize];decide
  have v12 : 12<caller.locals.size := by rw [callerSize];decide
  have sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra out.boolOutput.global := by rw [allocation];exact CurrentCallResourceSourceFinal.runtime out
  have sourceDistinct : Q.allocation.extra.roots.toList.Nodup := by rw [allocation];exact CurrentCallResourceSourceFinal.roots out
  have sourceRoom : Q.allocation.extra.nodes.size+1≤4294967295 := by
    rw [allocation]
    have room:=CurrentCallResourceBodyReadiness.current_nodes out ready
    omega
  have concrete : Q.pointer.value.provenance=.concrete id out.sourceOutput.tag := by rw [pointer];rfl
  have lenNonzero : len≠0 := by intro zero;have positive:=C.positive;rw [zero] at positive;contradiction
  have bounds:=CurrentCallResourceSharedStage.source_bounds out
  have qBounds : (UInt64.ofNat offset).toNat+len.toNat≤Q.allocation.extra.locations.size.bytes.toNat := by rw [allocation];exact bounds.2
  obtain ⟨rootNode,readerNode,distinct,rootSlot,rootAt,readerAt,readerTag,sourcePath,readerPath,primary⟩ :=
    stage_geometry Q sourceRuntime sourceDistinct out.sourceOutput.tag concrete (CurrentCallResourceBodyReadiness.current_room out ready)
      (UInt64.ofNat offset) len stage sourceRoom lenNonzero qBounds
  have treeEq : (child Q.allocation.extra out.boolOutput.global.protectedTags out.sourceOutput.tag out.boolOutput.global.nextPointerTag
      (UInt64.ofNat offset) len .VisitChildrenOfAccessed).tree=CurrentCallResourceSharedStage.tree out := by rw [allocation];rfl
  rw [treeEq] at distinct rootSlot rootAt readerAt sourcePath readerPath primary
  have currentRuntime : DuplicatePrefixBorrowContract.RuntimeFacts (entry out).allocation.extra current.global := by
    have known:=stage.runtime
    rw [treeEq] at known
    exact known
  have currentRows : GeneralRangeMapOrigins.OwnedOn (S05CurrentReadProtectorRelease.Authority (entry out).allocation.extra
      (S05ConcreteProtectedChildCompletion.extend Q.precise.completion stage.reader Q.pointer.grant) current.global.protectedTags
      stage.preparation.geometry.selectedRoot Q.pointer.grant stage.reader)
      (UInt64.ofNat offset) (UInt64.ofNat offset+len) (entry out).allocation.extra.locations := by
    have known:=stage.rows
    rw [treeEq] at known
    exact known
  have short : (entry out).allocation.extra.nodes.size<65536 := by
    have growth:=stage.growth
    rw [treeEq,allocation] at growth
    have initial:=CurrentCallResourceBodyReadiness.current_nodes out ready
    change (CurrentCallResourceSharedStage.tree out).nodes.size<65536
    omega
  have nodeRoom : (entry out).allocation.extra.nodes.size+1≤4294967295 := by omega
  have capacity : (entry out).allocation.extra.locations.size=(entry out).allocation.byteSize := by
    change (CurrentCallResourceSharedStage.tree out).locations.size=(CurrentCallResourceSourceFinal.entry out).allocation.byteSize
    have known:=stage.capacity
    rw [treeEq,allocation] at known
    exact known.trans (CurrentCallResourceEntryFacets.capacity out).1
  have currentBounds : (UInt64.ofNat offset).toNat+len.toNat≤(entry out).allocation.byteSize.bytes.toNat := by
    change (UInt64.ofNat offset).toNat+len.toNat≤(CurrentCallResourceSourceFinal.entry out).allocation.byteSize.bytes.toNat
    rw [←(CurrentCallResourceEntryFacets.capacity out).1]
    exact bounds.2
  have sourceModel:=CurrentCallResourceSharedStage.model out
  obtain ⟨ctx⟩:=ActualReferenceContext.exists_context options remaining span sourceModel.preciseOff sourceModel.implicitOff
  have enabled : machine.borrowTracker=some current := rfl
  have currentDefault : current.retagMode=.Default := by
    obtain ⟨old,enabled,mode⟩:=C.model.defaultTracker
    have same : old=tracker:=Option.some.inj (enabled.symm.trans C.state.enabled)
    subst old
    exact mode
  have machineData : machine.user.addresses=(CurrentCallResourceSharedStage.machine out).user.addresses ∧
      machine.user.payload.payload.user.types=(CurrentCallResourceSharedStage.machine out).user.payload.payload.user.types ∧
      machine.user.payload.payload.user.backend=(CurrentCallResourceSharedStage.machine out).user.payload.payload.user.backend := by
    dsimp only [machine,beforeMachine,CurrentCallResourceSharedStage.afterMachine,ReferenceBorrowDriver.allocatedMachine,
      PtrMetadataReturn.accountedMachine,SourceControl.accounted]
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl,rfl⟩
  have currentCached : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩ := by
    rw [machineData.1]
    exact cached
  have currentLive : machine.memory.live.find? (fun row=>row.1==id)=some (id,entry out) :=
    StackPopRelease.lookup_commit_same _ id (CurrentCallResourceSourceFinal.entry out) (CurrentCallResourceSharedStage.tree out)
  have currentGhost : machine.user.payload.ghost=false := by
    rw [PtrMetadataReturn.accounted_ghost]
    exact sourceModel.ghostOff
  have currentShallow : machine.user.payload.validation=.Shallow := by
    rw [PtrMetadataReturn.accounted_validation]
    exact sourceModel.shallow
  have currentRace : machine.dataRace=none := sourceModel.noDataRace
  have currentBackend : machine.user.payload.payload.user.backend=.none := machineData.2.2.trans sourceModel.noBackend
  have cell11 : caller.locals[11]=⟨.live (.immediate .uninit),none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem v11).symm.trans slot11)
  have live11 : caller.locals[11].value=.live (.immediate .uninit) := by rw [cell11]
  have uncached11 : caller.locals[11].layout=none := by rw [cell11]
  have sourceData := local_cell caller.locals 12 v12 rValue SharedReferenceMetadata.sharedLayout sourceSlot
  have sourceLive := sourceData.1
  have sourceCached := sourceData.2
  obtain ⟨thread,active,bound⟩:=stackReady
  have currentActive : machine.threads.activeThread?=some thread := by
    change out.finalMachine.threads.activeThread?=some thread
    rw [CurrentCallResourceEntryFacts.threads_eq out]
    exact active
  let rootCaller:=cachedCaller caller v11
  let destination:=(LocalPlaces.localRuntimePlace 0 rootCaller 11 RootCompilerFacts.usizeLayout).stackView
  let pushed:=LenPush.pushed options.userRelevantCrates (Storage.withCurrent #[] rootCaller machine) destination
  have pushedSize : pushed.stack.frames.size=2 := rfl
  obtain ⟨index,currentFrame,top,presentFrame⟩ := RelevanceCurrent.exists_current pushed.stack.frames thread (by rw [pushedSize];decide)
    (by intro index cached;have known:=bound index cached;rw [pushedSize];simpa using Nat.lt_trans known (by decide : 1<2))
  have pushedTypes : EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates
      (Storage.withCurrent #[] rootCaller machine) destination currentFrame)=machine.user.payload.payload.user.types := by
    let supply:=LenPush.fresh machine
    let helperFrame:=LenFrame.rawFrame options.userRelevantCrates supply.1 destination supply.2
    change (GenericPushRelevance.afterPush supply.1 1 helperFrame.extra.userRelevance currentFrame.extra.userRelevance).user.payload.payload.user.types=_
    rw [afterPush_types]
    rfl
  have metadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates
      (Storage.withCurrent #[] rootCaller machine) destination currentFrame)).metadata=PreparedReflection.actual.runtime := by
    rw [pushedTypes,machineData.2.1]
    exact sourceModel.metadata
  have origins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates
      (Storage.withCurrent #[] rootCaller machine) destination currentFrame)) := by
    rw [pushedTypes,machineData.2.1]
    exact CurrentCallResourceSharedStage.origins out
  have currentParents := stage.parents
  rw [treeEq] at currentParents
  obtain ⟨helper,post,⟨trace,location,returned,frameTracked,clocks,dest,cont,va,memory,tracked,ghost,shallow,race,addresses,types,extras⟩,facts,cache⟩ :=
    CurrentCallLenReadBody.before_return options limits remaining budget dispatch span ctx sourceModel.debugOff sourceModel.nullComparator
      C.dynamicFuel C.validationFuel C.dynamicEq C.validationEq id (entry out) base (UInt64.ofNat offset) len out.boolOutput.global.nextPointerTag
      (UInt64.lt_iff_toNat_lt.mpr C.positive) nonnull C.signedFits #[] caller machine current enabled currentDefault (helper_room out ready)
      (S05ConcreteProtectedChildCompletion.extend Q.precise.completion stage.reader Q.pointer.grant) currentRuntime currentParents distinct stage.preparation.geometry.selectedPosition stage.preparation.geometry.selectedRoot Q.pointer.grant stage.reader
      rootNode readerNode primary rootSlot rootAt sourcePath readerAt readerPath readerTag short nodeRoom currentRows currentBounds capacity
      v11 live11 uncached11 noClocks currentGhost currentShallow currentCached currentLive currentRace thread index currentFrame currentActive top presentFrame
      metadata origins sourceBody identity callee located (DuplicatePrefixCallModel.sourceComparator options remaining span _ sourceModel)
      v12 sourceLive sourceCached currentBackend beforeMachine rfl sourceModel.unchecked sourceModel.noGc sourceModel.fixedScheduler
  refine ⟨⟨helper,post,?_,location,returned,frameTracked,clocks,?_,cont,va,memory,tracked,ghost,shallow,race,addresses,types,extras,facts,cache⟩⟩
  · simpa only [callerEq,beforeMachine,ActualReferenceContext.config,Array.push_empty] using trace
  · simpa only [callerEq,Array.size_empty] using dest


/-- One actual shared producer supplies the correlated stage and address;
the Len call/body immediately consumes them and reaches the actual Return. -/
theorem invoke
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (budget : Nat) (dispatch : limits.callDispatch=budget+1) (nonzero : count≠0) :
    ∃ frame nextData nextOwner,
      ∃ Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩
          nextData nextOwner id offset len.toNat .mut,
      ∃ shape : GenericFunctionEntryPrefix.Shape (CurrentCallResourceEntry.finishedFrame out) frame count,
      ∃ stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len
          (CurrentCallResourceBodyReadiness.current_room out ready),
      ∃ base,∃ result : Returned out ready frame shape base,
        Q.pointer=CurrentCallResourceSourceAfterBool.pointer out ∧
        Q.allocation=(CurrentCallResourceSourceFinal.entry out).allocation ∧
        Q.precise.completion=CurrentCallResourceSourceFinal.completion out ∧
        SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
          (Storage.withCurrent #[] (CurrentCallResourceEntry.finishedFrame out) out.finalMachine)
          (Storage.withCurrent #[(cachedCaller (sharedFrame out frame shape base)
            (by rw [sharedFrame,shared_size out frame shape base];decide))] result.helper result.machine) := by
  obtain ⟨frame,nextData,nextOwner,Q,shape,pointer,allocation,completion,⟨stage⟩,base,cached,_,nonnull,sharedTrace⟩ :=
    CurrentCallResourceSharedInvoke.invoke_with_address out ready nonzero
  obtain ⟨result⟩ := before_return out ready stackReady budget dispatch frame shape Q pointer allocation stage base cached nonnull
  refine ⟨frame,nextData,nextOwner,Q,shape,stage,base,result,pointer,allocation,completion,?_⟩
  exact SuccessfulTrace.append sharedTrace result.trace

end
end DuplicatePrefix.CurrentCallResourceLenInvoke
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallResourceLenInvoke.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual uniform Len dependency {dependency}"
