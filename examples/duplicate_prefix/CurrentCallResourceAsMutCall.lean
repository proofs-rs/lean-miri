import duplicate_prefix.CurrentCallResourceAsMut
import duplicate_prefix.CurrentCallResourceLenRoots
import duplicate_prefix.GenericLenAcceptedPrelude
import duplicate_prefix.CurrentCallMutableReference
import duplicate_prefix.CurrentCallAsMutArgumentCopy
import duplicate_prefix.CurrentCallResourceFnEntry

namespace DuplicatePrefix.CurrentCallResourceAsMutCall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
open CanonicalConfigFacts ActualReferenceContext
open GeneralBorrowRawDefaultExpression RootReferenceInfo RootReferenceTrees GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

private theorem rvalue_of_steps
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator) (region : Region)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (base offset len : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (_defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (readCompleted : (GeneralBorrowRawDefaultExpression.read entry.allocation.extra tracker.global.protectedTags parentTag offset len .VisitChildrenOfAccessed).status = .Completed)
    (childCompleted : (GeneralBorrowRawDefaultExpression.child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).outcome = .ok ())
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (localId : MIR.LocalId) (different : localId ≠ 1)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : localId < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[localId].value = .live (.immediate .uninit))
    (destUncached : frame.locals[localId].layout = none)
    (query : CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler localId
      (Storage.withCurrent frames frame machine) = .ok (layout false) (Storage.withCurrent frames frame machine))
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine))) :
    let inner := config options remaining span
    let value := RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout false)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Ref region (RootReferenceRvalue.borrowKind false) ⟨1,#[.Deref]⟩) ⟨localId,#[]⟩ (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (ActualLocalCopy.written frame localId (layout false) validDest value.imm) resultMachine) := by
  have notConstructed := DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ metadata cacheOrigins
  let inner := config options remaining span
  let outer := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks outer limits
  let cachedFrame := LocalPlaces.cachePlaceLayout frame localId (layout false) validDest
  let activeTracker := {tracker with retagMode := mode false}
  let enteredMachine := RootReferenceRvalue.enter machine tracker false
  let updatedMachine := {ReferenceBorrowDriver.allocatedMachine enteredMachine activeTracker fresh with
    memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
  let value := RetagReferencePlace.sliceValue inner.access.runtime.base
    (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout false)
  let afterFrame := RootReferenceWrite.written cachedFrame localId value.imm
    (by simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validDest)
  have info := RootReferenceInfo.facts options remaining span ctx false
  have destination := ActualLocalPlace.uncached options limits (remaining+1) span debugOff frames frame machine
    localId (layout false) validDest destUncached info.sized query
  have cachedSourceValid : (1 : MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validSource
  have cachedDestValid : localId < cachedFrame.locals.size := by simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validDest
  have sourceLive' : cachedFrame.locals[1].value = .live (.immediate
      (PtrMetadataComplete.rawImmediate (.inl (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))) outer.access.runtime.base len)) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,different,PtrMetadataComplete.rawImmediate,RetagReferencePlace.sliceValue,outer] using sourceLive
  have sourceCached' : cachedFrame.locals[1].layout = some ActualReferenceMetadata.reference := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,different] using sourceCached
  have sourcePlace := RootReferencePlace.actual_slice_place options limits (remaining+1) span debugOff frames cachedFrame machine
    1 (.inl (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))) len cachedSourceValid sourceLive' sourceCached' noClocks ghost
  have destinationLive : cachedFrame.locals[localId].value = .live (.immediate .uninit) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using destLive
  have destinationCached : cachedFrame.locals[localId].layout = some (layout false) := by
    simp [cachedFrame,LocalPlaces.cachePlaceLayout]
  have entered : enteredMachine.borrowTracker = some activeTracker := rfl
  have current : activeTracker.retagMode = mode false := rfl
  have run := And.intro readCompleted childCompleted
  let parentTree := (read entry.allocation.extra tracker.global.protectedTags parentTag offset len .VisitChildrenOfAccessed).tree
  let resultTree := (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree
  have readTree : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read activeTracker.global.protectedTags .VisitChildrenOfAccessed).tree = parentTree := rfl
  have readDone : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read activeTracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := run.1
  have child' : parentTree.newChild (Size.ofBytes offset) (.concrete parentTag) activeTracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) (initial false)) (policy false).outsidePermission false =
      ⟨resultTree,.ok ()⟩ := by
    have succeeded := run.2
    change (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).outcome = .ok () at succeeded
    change child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed =
      ⟨(child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree,.ok ()⟩
    cases childEq : child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed with
    | mk treeResult result =>
      simp only [childEq] at succeeded
      cases succeeded
      rfl
  have physicalBounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat := by
    rw [←capacity]
    exact bounds
  have writer := RootReferenceWrite.positive_cached options limits remaining span ctx debugOff cmp false dynamicFuel validityFuel
    fuelEq validationFuel id entry base offset len parentTag positive nonzero signedFits physicalBounds
    frames cachedFrame enteredMachine activeTracker entered current fresh localId .uninit cachedDestValid destinationLive destinationCached
    noClocks ghost shallow cachedAddress present race parentTree (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree
    readTree readDone child' metadata notConstructed
  have baseEq : outer.access.runtime.base = inner.access.runtime.base := by
    rw [CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span,
      CanonicalConfigFacts.actual_access_runtime options () remaining span]
  have writer' : hooks.writeImmediate ()
      (PtrMetadataComplete.rawImmediate (.inl (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))) outer.access.runtime.base len)
      (LocalPlaces.localRuntimePlace frames.size cachedFrame localId (layout false))
      (Storage.withCurrent frames cachedFrame enteredMachine) = .ok () (Storage.withCurrent frames afterFrame updatedMachine) := by
    simpa only [hooks,outer,inner,afterFrame,value,activeTracker,baseEq,PtrMetadataComplete.rawImmediate,RetagReferencePlace.sliceValue,updatedMachine,enteredMachine,RootReferenceRvalue.enter] using writer
  have result := RootReferenceRvalue.of_write options limits (remaining+1) span false region
    (.inl (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))) len ⟨1,#[.Deref]⟩ ⟨localId,#[]⟩
    (LocalPlaces.localRuntimePlace frames.size cachedFrame localId (layout false)) (Storage.withCurrent frames frame machine)
    frames cachedFrame machine tracker (ReferenceBorrowDriver.allocatedTracker activeTracker fresh) enabled shallow rfl
    destination sourcePlace afterFrame updatedMachine rfl writer'
  simpa only [afterFrame,updatedMachine,enteredMachine,RootReferenceRvalue.enter,ReferenceBorrowDriver.allocatedMachine,
    ReferenceBorrowDriver.allocatedTracker,activeTracker,RootReferenceWrite.written,ActualLocalCopy.written,cachedFrame,value,
    inner] using result

private theorem statement_of_steps
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (base offset len : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir (RootReferenceFacts.location false))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (readCompleted : (GeneralBorrowRawDefaultExpression.read entry.allocation.extra tracker.global.protectedTags parentTag offset len .VisitChildrenOfAccessed).status = .Completed)
    (childCompleted : (GeneralBorrowRawDefaultExpression.child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).outcome = .ok ())
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : (RootReferenceFacts.destination false) < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[RootReferenceFacts.destination false].value = .live (.immediate .uninit))
    (destUncached : frame.locals[RootReferenceFacts.destination false].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine))) :
    let inner := config options remaining span
    let value := RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout false)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames (CopyHelperSteps.advance
        (ActualLocalCopy.written frame (RootReferenceFacts.destination false) (layout false) validDest value.imm)
        (RootReferenceFacts.location false)) resultMachine,.ok true) := by
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span preciseOff implicitOff
  have query := RootReferenceFacts.compute_destination frames frame machine sourceBody identity callee false
  have different : RootReferenceFacts.destination false ≠ 1 := by decide
  have rvalue := rvalue_of_steps options limits remaining span ctx debugOff cmp .Erased dynamicFuel validityFuel fuelEq validationFuel
    base offset len id entry positive nonzero signedFits frames frame machine tracker enabled
    defaultMode fresh parentTag bounds readCompleted childCompleted capacity (RootReferenceFacts.destination false) different validSource validDest sourceLive sourceCached
    destLive destUncached query noClocks ghost shallow cachedAddress present race metadata cacheOrigins
  let inner := config options remaining span
  let value := RetagReferencePlace.sliceValue inner.access.runtime.base
    (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout false)
  let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
    memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
  let resultFrame := ActualLocalCopy.written frame (RootReferenceFacts.destination false) (layout false) validDest value.imm
  apply CopyHelperSteps.assign_of_actual_rvalue (PreparedContracts.actualConfig options () (remaining+1) span) limits
    frames frame resultFrame machine resultMachine (RootReferenceFacts.location false)
    ⟨RootReferenceFacts.destination false,#[]⟩ (.Ref .Erased (RootReferenceRvalue.borrowKind false) ⟨1,#[.Deref]⟩) located
  · simpa [resultFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using located
  · rw [sourceBody]
    exact RootReferenceFacts.statement false
  · exact rvalue

private theorem child_facts {machine tracker data owner id offset len}
    (window : UniformWindow machine tracker data owner id offset.toNat len.toNat .mut)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts window.allocation.extra tracker.global)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (parentTag : BorTag) (concrete : window.pointer.value.provenance=.concrete id parentTag)
    (distinct : window.allocation.extra.roots.toList.Nodup) (short : window.allocation.extra.nodes.size<65536)
    (nodeRoom : window.allocation.extra.nodes.size+1≤4294967295)
    (nonzero : len≠0) (bounds : offset.toNat+len.toNat≤window.allocation.extra.locations.size.bytes.toNat)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex)
    (actual : CandidateCurrentFnEntryRaw.operation window.allocation.extra tracker.global {} id window.pointer.value.provenance offset len=.ok output)
    (lookup : output.child.tree.indexOfTag output.tag=some child) :
    (∃ node,output.child.tree.nodes.get child=some node ∧ node.tag=output.tag ∧ node.isExposed=false) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write offset (offset+len) ∧
      output.child.tree.nodes.size≤window.allocation.extra.nodes.size+1 ∧
      output.child.tree.roots=window.allocation.extra.roots ∧
      (∀ target,GeneralBorrowFreshActiveWithin.ActiveWithin window.allocation.extra target .Write offset (offset+len) →
        GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree target .Write offset (offset+len)) := by
  let literal:=CurrentCallTypedFnEntry.literal window.allocation.extra tracker.global {} id fresh (.concrete id parentTag) offset len
  have normalized:=CurrentCallTypedFnEntry.literal_operation window.allocation.extra tracker.global {} id fresh (.concrete id parentTag) offset len
  rw [concrete] at actual
  have outputEq : output=literal:=Except.ok.inj (actual.symm.trans normalized)
  have tagEq : output.tag=tracker.global.nextPointerTag:=by rw [outputEq];rfl
  obtain ⟨_,readRuntime,_,_,readNodes,readRoots,readTags,readCapacity⟩:=CurrentCallResourceFnEntry.prepare_read_selected window runtime {} fresh
    (by simp [CandidateCurrentGrantResources.demandOf]) distinct short offset len rfl rfl bounds
  simp only [concrete] at readRuntime readNodes readRoots readTags readCapacity
  let accessed:=literal.access.tree
  change DuplicatePrefixBorrowContract.RuntimeFacts accessed literal.global at readRuntime
  change accessed.nodes=window.allocation.extra.nodes at readNodes
  change accessed.roots=window.allocation.extra.roots at readRoots
  change accessed.tagMapping=window.allocation.extra.tagMapping at readTags
  change accessed.locations.size=window.allocation.extra.locations.size at readCapacity
  obtain ⟨parentNode,parentAt,_,binding⟩:=window.binding
  rw [concrete] at binding
  have parentTagEq : parentNode.tag=parentTag:=binding.2.symm
  have parentAfter : accessed.nodeAt window.pointer.grant=some parentNode:=by change accessed.nodes.get _=_;rw [readNodes];exact parentAt
  have parentTagged : accessed.indexOfTag parentTag=some window.pointer.grant:=by
    rw [←parentTagEq]
    exact readRuntime.formed.allocator.nodeTags _ _ parentAfter
  obtain ⟨_,_,_,_,_,originalFresh⟩:=GeneralBorrowFnEntryRegistrationRuntime.prepare window.allocation.extra tracker.global {} id fresh runtime
  have afterFresh : GeneralBorrowTagMap.Fresh accessed.tagMapping tracker.global.nextPointerTag:=by rw [readTags];exact originalFresh
  have afterRoom : accessed.nodes.size+1≤4294967295:=by rw [readNodes];exact nodeRoom
  have afterBounds : offset.toNat+len.toNat≤accessed.locations.size.bytes.toNat:=by rw [readCapacity];exact bounds
  obtain ⟨hiddenChild,hiddenLookup,⟨node,nodeAt,nodeTag,hidden⟩,_,_⟩:=GeneralBorrowProtectedChildMetadata.construct accessed literal.global readRuntime
    parentTag tracker.global.nextPointerTag window.pointer.grant parentNode parentTagged parentAfter afterFresh afterRoom offset len nonzero afterBounds
  have literalLookup : literal.child.tree.indexOfTag tracker.global.nextPointerTag=some child:=by simpa only [outputEq,literal,CurrentCallTypedFnEntry.literal] using lookup
  have hiddenLookup' : literal.child.tree.indexOfTag tracker.global.nextPointerTag=some hiddenChild:=by
    simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,
      accessed,GeneralBorrowFreshMetadataChildMutableSlot.result,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation] using hiddenLookup
  have sameChild : hiddenChild=child:=Option.some.inj (hiddenLookup'.symm.trans literalLookup)
  subst hiddenChild
  have hiddenNode : ∃ node,output.child.tree.nodes.get child=some node ∧ node.tag=output.tag ∧ node.isExposed=false:=by
    refine ⟨node,?_,nodeTag.trans tagEq.symm,hidden⟩
    rw [outputEq]
    simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,
      accessed,GeneralBorrowFreshMetadataChildMutableSlot.result,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using nodeAt
  obtain ⟨activeChild,activeLookup,activity⟩:=GeneralBorrowConstructorChildActivity.Protected.construct accessed literal.global readRuntime
    parentTag tracker.global.nextPointerTag window.pointer.grant parentNode parentTagged parentAfter afterFresh afterRoom offset len nonzero afterBounds
  have activeLookup' : literal.child.tree.indexOfTag tracker.global.nextPointerTag=some activeChild:=by
    simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,
      accessed,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation] using activeLookup
  have sameActive : activeChild=child:=Option.some.inj (activeLookup'.symm.trans literalLookup)
  subst activeChild
  have tagBound : tracker.global.nextPointerTag.value.toNat<literal.global.nextPointerTag.value.toNat:=by
    have successor:=GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag fresh
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat
    omega
  have held : literal.global.protectedTags.contains tracker.global.nextPointerTag=true:=by
    simp [literal,CurrentCallTypedFnEntry.literal,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,ProtectedTags.contains]
  obtain ⟨_,_,_,growth,other,otherLookup,leaf,_⟩:=CurrentCallParentInsertion.concrete_frame accessed literal.global readRuntime
    parentTag tracker.global.nextPointerTag window.pointer.grant parentNode parentTagged parentAfter afterFresh afterRoom tagBound held offset len nonzero afterBounds
  have resultEq : (accessed.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree=output.child.tree:=by
    rw [outputEq]
    rfl
  rw [resultEq] at activity growth leaf
  rw [readNodes] at growth
  have roots:=leaf.roots.trans readRoots
  refine ⟨hiddenNode,activity,growth,roots,?_⟩
  intro target active
  have readActivity : GeneralBorrowFreshActiveWithin.ActiveWithin accessed target .Write offset (offset+len):=
    GeneralBorrowFreshActiveWithinAccess.normal window.allocation.extra parentTag (Size.ofBytes offset) (Size.ofBytes len)
      .Read literal.global.protectedTags .VisitChildrenOfAccessed target offset (offset+len) runtime.formed.well bounds (Nat.le_refl _) (Nat.le_refl _) active
  have preserved:=GeneralBorrowRawTargetActivity.protected_child accessed literal.global readRuntime parentTag tracker.global.nextPointerTag
    window.pointer.grant parentNode parentTagged parentAfter afterFresh afterRoom offset len nonzero afterBounds target offset (offset+len)
    (Nat.le_refl _) (Nat.le_refl _) readActivity
  rw [resultEq] at preserved
  exact preserved

theorem caller_from_window
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    {data : Identities} {owner : Nat}
    (window : UniformWindow machine tracker data owner id offset.toNat len.toNat .mut)
    (allocationEq : window.allocation=entry.allocation)
    (concrete : window.pointer.value.provenance=.concrete id parentTag)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts window.allocation.extra tracker.global)
    (distinct : window.allocation.extra.roots.toList.Nodup)
    (short : window.allocation.extra.nodes.size<65536)
    (nodeRoom : window.allocation.extra.nodes.size+1≤4294967295)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (destValid : (15 : MIR.LocalId) < caller.locals.size) (old : Immediate Provenance)
    (destLive : caller.locals[15].value = .live (.immediate old))
    (uncached : caller.locals[15].layout = none)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)))
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) machine)
      (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) machine)
      (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current)
    (source : PreparedContracts.SourceComparator)
    (sourceBody : caller.body = RootBody.reflected.body.body)
    (sourceIdentity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (sourceCallee : caller.functionInstance = RootBody.reflected.functionInstance)
    (sourceLocation : caller.location = .mir ⟨6,8⟩)
    (valid16 : (16 : MIR.LocalId) < caller.locals.size)
    (value16 : caller.locals[16].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (cached16 : caller.locals[16].layout = some ActualReferenceMetadata.reference)
    (backend : machine.user.payload.payload.user.backend = .none) :
    ∃ output child,
      CandidateCurrentFnEntryRaw.operation window.allocation.extra tracker.global {} id window.pointer.value.provenance offset len=.ok output ∧
      output.tag=tracker.global.nextPointerTag ∧ output.global=(GeneralBorrowFnEntryRegistration.registered tracker.global {} id fresh).1 ∧
      output.frame=(GeneralBorrowFnEntryRegistration.registered tracker.global {} id fresh).2 ∧
      output.child.tree.indexOfTag output.tag=some child ∧
      Nonempty (CurrentCallResourceFnEntry.BorrowWitness window output child offset len) ∧
      (∃ node,output.child.tree.nodes.get child=some node ∧ node.tag=output.tag ∧ node.isExposed=false) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write offset (offset+len) ∧
      output.child.tree.nodes.size≤window.allocation.extra.nodes.size+1 ∧ output.child.tree.roots=window.allocation.extra.roots ∧
      (∀ target,GeneralBorrowFreshActiveWithin.ActiveWithin window.allocation.extra target .Write offset (offset+len) →
        GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree target .Write offset (offset+len)) ∧
      output.child.tree=CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len ∧
    let cfg := config options remaining span
    let before := Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) machine
    let destination := (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
    let finalTree := CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    let frame := CurrentCallAsMutArgumentCopy.Entry.initialized options before destination value adjusted id tracker.global.nextPointerTag
    ∃ done : CompilerFrameContext.ActualFrame,
    Call.evalCallTerminator (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      () limits.callDispatch AsMutEvaluateCall.terminator (Storage.withCurrent #[] caller machine) =
      .ok () (Storage.withCurrent (#[(AsMutUncachedCall.cachedCaller caller destValid)])
        (CurrentCallAsMutArgumentCopy.Entry.initialized options before destination value adjusted id tracker.global.nextPointerTag) resultMachine) ∧
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent (#[(AsMutUncachedCall.cachedCaller caller destValid)]) frame resultMachine)
        (Storage.withCurrent (#[(AsMutUncachedCall.cachedCaller caller destValid)]) done resultMachine) ∧
      done.location = .mir ⟨0,10⟩ ∧
      done.locals[0]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer
        (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)))))),some CopyCompilerFacts.destPointerLayout⟩ ∧
      done.body = frame.body ∧ done.bodyIdentity = frame.bodyIdentity ∧
      done.functionInstance = frame.functionInstance ∧
      done.extra = frame.extra ∧ done.returnPlace = frame.returnPlace ∧ done.returnContinuation = frame.returnContinuation ∧
      done.vaList = frame.vaList ∧ done.localsIdentity = frame.localsIdentity ∧
      done.locals[1]? = frame.locals[1]? ∧ done.locals.size = 5 ∧
      (done.locals[2]?.map (·.value)) = some .dead ∧
      (done.locals[3]?.map (·.value)) = some .dead ∧
      (done.locals[4]?.map (·.value)) = some .dead := by
  have nonzeroLen : len≠0:=by intro zero;subst len;simp at positive
  have treeBounds : offset.toNat+len.toNat≤window.allocation.extra.locations.size.bytes.toNat:=by rw [allocationEq,capacity];exact bounds
  obtain ⟨output,child,operation,tag,global,frame,readDone,childDone,lookup,witness⟩:=CurrentCallResourceFnEntry.correlated_borrow_selected
    window runtime {} fresh (by simp [CandidateCurrentGrantResources.demandOf]) distinct short nodeRoom offset len rfl rfl nonzeroLen treeBounds
  have actual:=operation
  rw [allocationEq,concrete] at actual
  let literal:=CurrentCallTypedFnEntry.literal entry.allocation.extra tracker.global {} id fresh (.concrete id parentTag) offset len
  have normalized : CandidateCurrentFnEntryRaw.operation entry.allocation.extra tracker.global {} id (.concrete id parentTag) offset len=.ok literal:=
    CurrentCallTypedFnEntry.literal_operation entry.allocation.extra tracker.global {} id fresh (.concrete id parentTag) offset len
  have outputEq : output=literal:=Except.ok.inj (actual.symm.trans normalized)
  have readCompleted : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).status=.Completed:=by
    simpa only [outputEq,literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,
      GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,TypedBorrowSteps.registeredGlobal,
      GlobalState.addProtector,FrameState.addProtector] using readDone
  have childCompleted : ((entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree.newChild
      (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome=.ok ():=by
    simpa only [outputEq,literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,
      GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,TypedBorrowSteps.registeredGlobal,
      GlobalState.addProtector,FrameState.addProtector,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation] using childDone
  have treeEq : output.child.tree=CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len:=by rw [outputEq];rfl
  obtain ⟨hidden,activity,growth,roots,targetActivity⟩:=child_facts window runtime fresh parentTag concrete distinct short nodeRoom nonzeroLen treeBounds output child operation lookup
  refine ⟨output,child,operation,tag,global,frame,lookup,witness,hidden,activity,growth,roots,targetActivity,treeEq,?_⟩
  exact CurrentCallAsMutArgumentCopy.Body.caller_before_return options limits remaining budget dispatchFuel span ctx debugOff cmp
    dynamicFuel validityFuel fuelEq validationEq id entry base offset len parentTag positive nonzero signedFits bounds caller machine tracker enabled defaultMode fresh
    readCompleted childCompleted capacity destValid old destLive uncached callerClocks ghost shallow cachedAddress present race metadata cacheOrigins
    thread index current active top topPresent source sourceBody sourceIdentity sourceCallee sourceLocation valid16 value16 cached16 backend

private theorem spatial_world {before tracker id allocation completion grant}
    (issued : SpatialDelegation before tracker id allocation completion grant)
    (post : Before) (present : Present (ActualWorld post) id allocation) :
    SpatialDelegation post tracker id allocation completion grant := by
  induction issued with
  | allocated cap => exact .allocated {cap with live:=present}
  | concrete _ path ih => exact .concrete ih path
  | @wildcard origin root originNode rootNode earlier position originRoot issued originAt exposed rootAt parentless older earlierPosition earlierAt rootSlot path edge ih =>
    exact .wildcard originNode rootNode earlier position originRoot ih originAt exposed rootAt parentless older earlierPosition earlierAt rootSlot path edge

def accountedWindow (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    {machine tracker data owner id offset length}
    (window : UniformWindow machine tracker data owner id offset length .mut) :
    UniformWindow (AsMutPtrReturn.accountedMachine options remaining span machine) tracker data owner id offset length .mut := by
  have present : Present (ActualWorld (AsMutPtrReturn.accountedMachine options remaining span machine)) id window.allocation:=window.present
  exact {window with present:=present,issued:=spatial_world window.issued _ present}

theorem step_from_window
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    {data : Identities} {owner : Nat}
    (window : UniformWindow machine tracker data owner id offset.toNat len.toNat .mut)
    (allocationEq : window.allocation=entry.allocation)
    (concrete : window.pointer.value.provenance=.concrete id parentTag)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts window.allocation.extra tracker.global)
    (distinct : window.allocation.extra.roots.toList.Nodup)
    (short : window.allocation.extra.nodes.size<65536)
    (nodeRoom : window.allocation.extra.nodes.size+1≤4294967295)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (destValid : (15 : MIR.LocalId) < caller.locals.size) (old : Immediate Provenance)
    (destLive : caller.locals[15].value = .live (.immediate old))
    (uncached : caller.locals[15].layout = none)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)))
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current)
    (source : PreparedContracts.SourceComparator)
    (sourceBody : caller.body = RootBody.reflected.body.body)
    (sourceIdentity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (sourceCallee : caller.functionInstance = RootBody.reflected.functionInstance)
    (sourceLocation : caller.location = .mir ⟨6,8⟩)
    (valid16 : (16 : MIR.LocalId) < caller.locals.size)
    (value16 : caller.locals[16].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (cached16 : caller.locals[16].layout = some ActualReferenceMetadata.reference)
    (backend : machine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true) :

    ∃ output child,
      CandidateCurrentFnEntryRaw.operation window.allocation.extra tracker.global {} id window.pointer.value.provenance offset len=.ok output ∧
      output.tag=tracker.global.nextPointerTag ∧ output.global=(GeneralBorrowFnEntryRegistration.registered tracker.global {} id fresh).1 ∧
      output.frame=(GeneralBorrowFnEntryRegistration.registered tracker.global {} id fresh).2 ∧
      output.child.tree.indexOfTag output.tag=some child ∧
      Nonempty (CurrentCallResourceFnEntry.BorrowWitness (accountedWindow options remaining span window) output child offset len) ∧
      (∃ node,output.child.tree.nodes.get child=some node ∧ node.tag=output.tag ∧ node.isExposed=false) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write offset (offset+len) ∧
      output.child.tree.nodes.size≤window.allocation.extra.nodes.size+1 ∧ output.child.tree.roots=window.allocation.extra.roots ∧
      (∀ target,GeneralBorrowFreshActiveWithin.ActiveWithin window.allocation.extra target .Write offset (offset+len) →
        GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree target .Write offset (offset+len)) ∧
      output.child.tree=CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len ∧
    let cfg := config options remaining span
    let before := Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine)
    let destination := (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
    let finalTree := CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    let frame := CurrentCallAsMutArgumentCopy.Entry.initialized options before destination value adjusted id tracker.global.nextPointerTag
    ∃ done : CompilerFrameContext.ActualFrame,
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent #[] caller machine) =
      ((Storage.withCurrent (#[(AsMutUncachedCall.cachedCaller caller destValid)])
        (CurrentCallAsMutArgumentCopy.Entry.initialized options before destination value adjusted id tracker.global.nextPointerTag) resultMachine),.ok true) ∧
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent (#[(AsMutUncachedCall.cachedCaller caller destValid)]) frame resultMachine)
        (Storage.withCurrent (#[(AsMutUncachedCall.cachedCaller caller destValid)]) done resultMachine) ∧
      done.location = .mir ⟨0,10⟩ ∧
      done.locals[0]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer
        (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)))))),some CopyCompilerFacts.destPointerLayout⟩ ∧
      done.body = frame.body ∧ done.bodyIdentity = frame.bodyIdentity ∧
      done.functionInstance = frame.functionInstance ∧
      done.extra = frame.extra ∧ done.returnPlace = frame.returnPlace ∧ done.returnContinuation = frame.returnContinuation ∧
      done.vaList = frame.vaList ∧ done.localsIdentity = frame.localsIdentity ∧
      done.locals[1]? = frame.locals[1]? ∧ done.locals.size = 5 ∧
      (done.locals[2]?.map (·.value)) = some .dead ∧
      (done.locals[3]?.map (·.value)) = some .dead ∧
      (done.locals[4]?.map (·.value)) = some .dead ∧
      GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts options remaining span resultMachine resultMachine ∧
      GeneralBorrowForestMixedLenBeforeReturn.RootCache #[] resultMachine ∧
      done.extra.borrowTracker = some output.frame ∧ done.extra.dataRace = none ∧
      done.body = HelperCompilerFacts.asMutPtrBody.body ∧
      done.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout ∧
      done.returnContinuation = .goto (some 7) .Continue ∧ done.vaList = #[] ∧
      done.locals[1]? = some ⟨.live (.immediate adjusted),some ActualReferenceMetadata.reference⟩ := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let initial := Storage.withCurrent #[] caller machine
  let next := AsMutPtrReturn.accountedMachine options remaining span machine
  let nextState := Storage.withCurrent #[] caller next
  have nextGhost : next.user.payload.ghost = false := (AsMutPtrReturn.accounted_ghost options remaining span machine).trans ghost
  have nextShallow : next.user.payload.validation = .Shallow := (AsMutPtrReturn.accounted_validation options remaining span machine).trans shallow
  have nextBackend : next.user.payload.payload.user.backend = .none := by
    unfold next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact backend
  have nextAddress : next.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    unfold next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact cachedAddress
  have nextMetadata : (EvalProjectionMachine.arrays.get nextState).metadata = PreparedReflection.actual.runtime := by
    unfold nextState next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact metadata
  have nextOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get nextState) := by
    unfold nextState next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact cacheOrigins
  let nextWindow:=accountedWindow options remaining span window
  obtain ⟨output,child,actual,tag,global,frameEq,lookup,witness,hidden,activity,growth,roots,targetActivity,treeEq,bodyResult⟩ :=
    caller_from_window options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id entry base offset len parentTag positive nonzero signedFits bounds caller next tracker enabled defaultMode fresh
      nextWindow allocationEq concrete runtime distinct short nodeRoom capacity
      destValid old destLive uncached callerClocks nextGhost nextShallow nextAddress present race nextMetadata nextOrigins
      thread index current active top topPresent source sourceBody sourceIdentity sourceCallee sourceLocation valid16 value16 cached16 nextBackend
  change CandidateCurrentFnEntryRaw.operation window.allocation.extra tracker.global {} id window.pointer.value.provenance offset len=.ok output at actual
  obtain ⟨done,called,trace,location,pointerDone,body,identity,callee,extra,returnPlace,continuation,varargs,localsId,sourceSlot,sizeDone,dead2,dead3,dead4⟩ := bodyResult
  let root := AsMutUncachedCall.cachedCaller caller destValid
  let beforePush := Storage.withCurrent #[] root next
  let destination := (LocalPlaces.localRuntimePlace 0 root 15 CopyCompilerFacts.destPointerLayout).stackView
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let post := (AsMutPush.completed options.userRelevantCrates beforePush destination current).machine
  let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine post tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory post.memory id entry (CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len)}
  let frame := CurrentCallAsMutArgumentCopy.Entry.initialized options beforePush destination value adjusted id tracker.global.nextPointerTag
  have frameExtra : done.extra = frame.extra := extra
  obtain ⟨_,_,postRace,postAddress,postGhost,postShallow,postUser,postFixed⟩ :=
    AsMutPushPreserves.preserves options.userRelevantCrates beforePush destination current
  change post.user.payload.payload.user = next.user.payload.payload.user at postUser
  have helperGhost : resultMachine.user.payload.ghost = false := by
    change post.user.payload.ghost = false
    exact postGhost.trans nextGhost
  have helperShallow : resultMachine.user.payload.validation = .Shallow := by
    change post.user.payload.validation = .Shallow
    exact postShallow.trans nextShallow
  have helperRace : resultMachine.dataRace = none := by
    change post.dataRace = none
    exact postRace.trans race
  have helperBackend : resultMachine.user.payload.payload.user.backend = .none := by
    change post.user.payload.payload.user.backend = .none
    rw [postUser]
    exact nextBackend
  have nextFlags := RootZeroCompleteState.tick_flags options remaining span machine
  have nextUnchecked : (cfg.terminators.getControl next.user).checkedArithmetic = false := nextFlags.1.trans unchecked
  have nextNoGc : (cfg.terminators.getControl next.user).gcInterval = 0 := nextFlags.2.trans noGc
  have helperUnchecked : (cfg.terminators.getControl resultMachine.user).checkedArithmetic = false := by
    change (cfg.terminators.getControl post.user).checkedArithmetic = false
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] at nextUnchecked ⊢
    simp only [EvalTerminatorMachine.genericHooks] at nextUnchecked ⊢
    rw [postUser]
    exact nextUnchecked
  have helperNoGc : (cfg.terminators.getControl resultMachine.user).gcInterval = 0 := by
    change (cfg.terminators.getControl post.user).gcInterval = 0
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] at nextNoGc ⊢
    simp only [EvalTerminatorMachine.genericHooks] at nextNoGc ⊢
    rw [postUser]
    exact nextNoGc
  have helperFixed : resultMachine.threads.fixedScheduling = true := by
    change post.threads.fixedScheduling = true
    exact postFixed.trans fixed
  let supply := AsMutPush.fresh next
  let rank := (AsMutFrame.rawFrame options.userRelevantCrates supply.1 destination supply.2).extra.userRelevance
  let nextThread := if rank >= current.extra.userRelevance then {thread with topUserRelevantFrame := some 1} else thread
  have helperActive : resultMachine.threads.activeThread? = some nextThread := by
    change (GenericPushRelevance.afterPush supply.1 1 rank current.extra.userRelevance).threads.activeThread? = some nextThread
    exact AsMutPushPreserves.active_after_push supply.1 thread active 1 rank current.extra.userRelevance
  have indexBound : index < 2 := by
    have known := (Array.getElem?_eq_some_iff.mp topPresent).1
    simpa only [AsMutPush.pushed,Storage.withCurrent,Array.size_push,Array.size_empty] using known
  have oldBound (i : Nat) (same : thread.topUserRelevantFrame = some i) : i < 2 := by
    have equal : i = index := by simpa only [FrameRelevance.top,same,Option.orElse_some,Option.some.injEq] using top
    simpa only [equal] using indexBound
  have cacheBound (i : Nat) (same : nextThread.topUserRelevantFrame = some i) : i < 2 := by
    unfold nextThread at same
    split at same
    · have equal : (1 : Nat) = i := by simpa only [Option.some.injEq] using same
      omega
    · exact oldBound i same
  have helperRuntime : GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts options remaining span resultMachine resultMachine :=
    ⟨helperGhost,helperShallow,helperRace,rfl,rfl,rfl,helperBackend,helperUnchecked,helperNoGc,helperFixed,⟨nextThread,helperActive⟩⟩
  have helperCache : GeneralBorrowForestMixedLenBeforeReturn.RootCache #[] resultMachine :=
    ⟨fun _ => ⟨nextThread,helperActive,cacheBound⟩⟩
  let literal := CurrentCallTypedFnEntry.literal entry.allocation.extra tracker.global {} id fresh (.concrete id parentTag) offset len
  have normalized : CandidateCurrentFnEntryRaw.operation entry.allocation.extra tracker.global {} id (.concrete id parentTag) offset len=.ok literal :=
    CurrentCallTypedFnEntry.literal_operation entry.allocation.extra tracker.global {} id fresh (.concrete id parentTag) offset len
  have actualConcrete:=actual
  rw [allocationEq,concrete] at actualConcrete
  have outputEq : output=literal:=Except.ok.inj (actualConcrete.symm.trans normalized)
  have helperBorrow : done.extra.borrowTracker = some output.frame := by
    rw [frameExtra,outputEq]
    rfl
  have frameRace : frame.extra.dataRace = none := by
    change machine.dataRace.map _ = none
    rw [race]
    rfl
  have helperClocks : done.extra.dataRace = none := by rw [frameExtra];exact frameRace
  have helperBody : done.body = HelperCompilerFacts.asMutPtrBody.body := body
  have helperDestination : done.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace 0 root 15 CopyCompilerFacts.destPointerLayout := by
    rw [returnPlace]
    rfl
  have helperContinuation : done.returnContinuation = .goto (some 7) .Continue := by rw [continuation];rfl
  have helperVarargs : done.vaList = #[] := by rw [varargs];rfl
  have slots := GeneralBorrowRawAsMutShape.locals options beforePush destination value adjusted id tracker.global.nextPointerTag
  have helperOne : done.locals[1]? = some ⟨.live (.immediate adjusted),some ActualReferenceMetadata.reference⟩ := by
    rw [sourceSlot]
    change frame.locals[1]? = _
    rw [show frame.locals = _ from slots]
    rfl
  have accounting := SourceControl.before_terminator cfg limits () initial
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have accounting' : (ExecutionMachine.stepHooks cfg limits).beforeTerminator () initial = (nextState,.ok ()) := accounting
  let block := RootBody.reflected.body.body.basicBlocks[6]'(by with_unfolding_all decide +kernel)
  have blockAt : caller.body.basicBlocks[6]? = some block := by rw [sourceBody];simp [block]
  have noStatement : block.statements[8]? = none := by with_unfolding_all rfl
  refine ⟨output,child,actual,tag,global,frameEq,lookup,witness,hidden,activity,growth,roots,targetActivity,treeEq,done,?_,
    trace,location,pointerDone,body,identity,callee,extra,returnPlace,continuation,varargs,localsId,sourceSlot,sizeDone,dead2,dead3,dead4,helperRuntime,helperCache,helperBorrow,helperClocks,helperBody,helperDestination,helperContinuation,helperVarargs,helperOne⟩
  apply GenericCallStages.source_step cfg limits () initial nextState _ caller ⟨6,8⟩ block
    HelperCompilerFacts.asMutPtrCall.function #[AsMutEvaluateCall.argument] ⟨15,#[]⟩ (some 7) .Continue
    AsMutCallTerminator.sourceKind AsMutCallTerminator.fnSpan
    (by simp [initial,Storage.withCurrent,Stack.currentFrame?]) sourceLocation blockAt noStatement AsMutCallTerminator.source_call accounting' called
  simp [Storage.withCurrent,nextState]


/-- One actual mutable helper call/body and its SAME selected borrow witness. -/
structure Seed (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    {before : Before} {tracker : MachineHooks.BorrowState} {data : Identities} {owner : Nat}
    {id : AllocId} {offset len : UInt64}
    (window : UniformWindow before tracker data owner id offset.toNat len.toNat .mut)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (caller : CompilerFrameContext.ActualFrame)
    (base : UInt64) (parentTag : BorTag) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (valid15 : (15 : MIR.LocalId)<caller.locals.size) where
  allocationEq : window.allocation=entry.allocation
  pointerEq : window.pointer.value=Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))
  beforeRuntime : DuplicatePrefixBorrowContract.RuntimeFacts window.allocation.extra tracker.global
  mode : tracker.retagMode=.Default
  output : GeneralBorrowForestFnEntry.Output
  childIndex : UniIndex
  operation : CandidateCurrentFnEntryRaw.operation window.allocation.extra tracker.global {} id window.pointer.value.provenance offset len=.ok output
  tag : output.tag=tracker.global.nextPointerTag
  global : output.global=(GeneralBorrowFnEntryRegistration.registered tracker.global {} id fresh).1
  frameEq : output.frame=(GeneralBorrowFnEntryRegistration.registered tracker.global {} id fresh).2
  lookup : output.child.tree.indexOfTag output.tag=some childIndex
  witness : CurrentCallResourceFnEntry.BorrowWitness (accountedWindow options remaining span window) output childIndex offset len
  hidden : ∃ node,output.child.tree.nodes.get childIndex=some node ∧ node.tag=output.tag ∧ node.isExposed=false
  activity : GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree childIndex .Write offset (offset+len)
  growth : output.child.tree.nodes.size≤window.allocation.extra.nodes.size+1
  roots : output.child.tree.roots=window.allocation.extra.roots
  distinct : output.child.tree.roots.toList.Nodup
  targetActivity : ∀ target,GeneralBorrowFreshActiveWithin.ActiveWithin window.allocation.extra target .Write offset (offset+len) →
    GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree target .Write offset (offset+len)
  positive : (0 : UInt64)<len
  bounds : offset.toNat+len.toNat≤output.child.tree.locations.size.bytes.toNat
  short : output.child.tree.nodes.size<65536
  helper : CompilerFrameContext.ActualFrame
  machine : Before
  trace : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
    (Storage.withCurrent #[] caller before)
    (Storage.withCurrent #[(AsMutUncachedCall.cachedCaller caller valid15)] helper machine)
  memory : machine.memory=RetagEntry.updatedMemory before.memory id entry output.child.tree
  addresses : machine.user.addresses=before.user.addresses
  types : machine.user.payload.payload.user.types=before.user.payload.payload.user.types
  extras : machine.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras
  live : machine.memory.live.find? (fun row=>row.1==id)=some (id,{entry with allocation:=entry.allocation.setExtra output.child.tree})
  tracked : machine.borrowTracker=some {tracker with global:=output.global}
  runtime : GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts options remaining span machine machine
  cache : GeneralBorrowForestMixedLenBeforeReturn.RootCache #[] machine
  borrow : helper.extra.borrowTracker=some output.frame
  frameOwned : output.frame.protectedTags=#[(id,output.tag)]
  clocks : helper.extra.dataRace=none
  body : helper.body=HelperCompilerFacts.asMutPtrBody.body
  location : helper.location=.mir ⟨0,10⟩
  size : helper.locals.size=5
  returned : helper.locals[0]?=some ⟨.live (.immediate (.scalar (Scalar.fromPointer
    (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
    (Pointer.new (.concrete id output.tag) (Size.ofBytes (base+offset)))))),some CopyCompilerFacts.destPointerLayout⟩
  argument : Immediate Provenance
  argumentAt : helper.locals[1]?.map (·.value)=some (.live (.immediate argument))
  dead2 : helper.locals[2]?.map (·.value)=some .dead
  dead3 : helper.locals[3]?.map (·.value)=some .dead
  dead4 : helper.locals[4]?.map (·.value)=some .dead
  destination : helper.returnPlace.toRuntimePlace=LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller valid15) 15 CopyCompilerFacts.destPointerLayout
  continuation : helper.returnContinuation=.goto (some 7) .Continue
  varargs : helper.vaList=#[]
  callerValid : (15 : MIR.LocalId)<(AsMutUncachedCall.cachedCaller caller valid15).locals.size
  callerLive : (AsMutUncachedCall.cachedCaller caller valid15).locals[15].value=.live (.immediate .uninit)
  callerCached : (AsMutUncachedCall.cachedCaller caller valid15).locals[15].layout=some CopyCompilerFacts.destPointerLayout
  callerClocks : (AsMutUncachedCall.cachedCaller caller valid15).extra.dataRace=none

theorem seed_from_window
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    {data : Identities} {owner : Nat}
    (window : UniformWindow machine tracker data owner id offset.toNat len.toNat .mut)
    (allocationEq : window.allocation=entry.allocation)
    (concrete : window.pointer.value.provenance=.concrete id parentTag)
    (pointerEq : window.pointer.value=Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts window.allocation.extra tracker.global)
    (distinct : window.allocation.extra.roots.toList.Nodup)
    (short : window.allocation.extra.nodes.size<65536)
    (nodeRoom : window.allocation.extra.nodes.size+1≤4294967295)
    (nodeMargin : window.allocation.extra.nodes.size+1<65536)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (destValid : (15 : MIR.LocalId) < caller.locals.size)
    (destLive : caller.locals[15].value = .live (.immediate .uninit))
    (uncached : caller.locals[15].layout = none)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)))
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current)
    (source : PreparedContracts.SourceComparator)
    (sourceBody : caller.body = RootBody.reflected.body.body)
    (sourceIdentity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (sourceCallee : caller.functionInstance = RootBody.reflected.functionInstance)
    (sourceLocation : caller.location = .mir ⟨6,8⟩)
    (valid16 : (16 : MIR.LocalId) < caller.locals.size)
    (value16 : caller.locals[16].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (cached16 : caller.locals[16].layout = some ActualReferenceMetadata.reference)
    (backend : machine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true) : Nonempty (Seed options limits remaining span window entry caller base parentTag fresh destValid) := by
  obtain ⟨output,child,operation,tag,global,frameEq,lookup,⟨witness⟩,hidden,activity,growth,roots,targetActivity,treeEq,
    done,step,trace,location,pointerDone,body,identity,callee,extra,returnPlace,continuation,varargs,localsId,sourceSlot,sizeDone,
    dead2,dead3,dead4,helperRuntime,helperCache,helperBorrow,helperClocks,helperBody,helperDestination,helperContinuation,helperVarargs,helperOne⟩ :=
    step_from_window options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id entry base offset len parentTag positive nonzero signedFits bounds caller machine tracker enabled defaultMode fresh
      window allocationEq concrete runtime distinct short nodeRoom capacity destValid .uninit destLive uncached callerClocks ghost shallow cachedAddress present race metadata cacheOrigins
      thread index current active top topPresent source sourceBody sourceIdentity sourceCallee sourceLocation valid16 value16 cached16 backend unchecked noGc fixed
  let root:=AsMutUncachedCall.cachedCaller caller destValid
  let next:=AsMutPtrReturn.accountedMachine options remaining span machine
  let beforePush:=Storage.withCurrent #[] root next
  let destination:=(LocalPlaces.localRuntimePlace 0 root 15 CopyCompilerFacts.destPointerLayout).stackView
  let post:=(AsMutPush.completed options.userRelevantCrates beforePush destination current).machine
  let finalTree:=CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len
  let resultMachine:={TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine post tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
    memory:=RetagEntry.updatedMemory post.memory id entry finalTree}
  let argument:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  obtain ⟨postMemory,_,_,postAddresses,_,_,postUser,_⟩:=AsMutPushPreserves.preserves options.userRelevantCrates beforePush destination current
  have memoryEq : resultMachine.memory=RetagEntry.updatedMemory machine.memory id entry output.child.tree:=by
    change RetagEntry.updatedMemory post.memory id entry finalTree=_
    rw [postMemory]
    change RetagEntry.updatedMemory machine.memory id entry finalTree=_
    dsimp only [finalTree]
    rw [←treeEq]
  have trackedEq : resultMachine.borrowTracker=some {tracker with global:=output.global}:=by
    change some (TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag)=_
    rw [global]
    rfl
  have currentLive : resultMachine.memory.live.find? (fun row=>row.1==id)=some (id,{entry with allocation:=entry.allocation.setExtra output.child.tree}):=by
    rw [memoryEq]
    exact StackPopRelease.lookup_commit_same _ _ _ _
  have currentAddress : resultMachine.user.addresses=machine.user.addresses:=by
    change post.user.addresses=machine.user.addresses
    rw [postAddresses]
    change next.user.addresses=machine.user.addresses
    unfold next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have currentTypes : resultMachine.user.payload.payload.user.types=machine.user.payload.payload.user.types:=by
    change post.user.payload.payload.user.types=machine.user.payload.payload.user.types
    change post.user.payload.payload.user=next.user.payload.payload.user at postUser
    rw [postUser]
    unfold next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have currentExtras : resultMachine.user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras:=by
    change post.user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras
    change post.user.payload.payload.user=next.user.payload.payload.user at postUser
    rw [postUser]
    unfold next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have frameOwned : output.frame.protectedTags=#[(id,output.tag)]:=by
    rw [frameEq,tag]
    simp only [GeneralBorrowFnEntryRegistration.registered,GlobalState.addProtector,FrameState.addProtector,Array.push_empty]
  have outputBounds : offset.toNat+len.toNat≤output.child.tree.locations.size.bytes.toNat:=by
    rw [witness.capacity]
    change offset.toNat+len.toNat≤window.allocation.extra.locations.size.bytes.toNat
    rw [allocationEq,capacity]
    exact bounds
  have outputShort : output.child.tree.nodes.size<65536:=by omega
  have outputDistinct : output.child.tree.roots.toList.Nodup:=by rw [roots];exact distinct
  have rootValid : (15 : MIR.LocalId)<root.locals.size:=by simpa only [root,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.size_set] using destValid
  have rootLive : root.locals[15].value=.live (.immediate .uninit):=by simpa only [root,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self] using destLive
  have rootCached : root.locals[15].layout=some CopyCompilerFacts.destPointerLayout:=by simp [root,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout]
  have argumentAt : done.locals[1]?.map (·.value)=some (.live (.immediate argument)):=by
    simpa only [Option.map_some] using congrArg (Option.map LocalState.value) helperOne
  have returned : done.locals[0]?=some ⟨.live (.immediate (.scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id output.tag) (Size.ofBytes (base+offset)))))),some CopyCompilerFacts.destPointerLayout⟩:=by
    rw [tag]
    exact pointerDone
  refine ⟨{
    allocationEq:=allocationEq
    pointerEq:=pointerEq
    beforeRuntime:=runtime
    mode:=defaultMode
    output:=output
    childIndex:=child
    operation:=operation
    tag:=tag
    global:=global
    frameEq:=frameEq
    lookup:=lookup
    witness:=witness
    hidden:=hidden
    activity:=activity
    growth:=growth
    roots:=roots
    distinct:=outputDistinct
    targetActivity:=targetActivity
    positive:=positive
    bounds:=outputBounds
    short:=outputShort
    helper:=done
    machine:=resultMachine
    trace:=.next step trace
    memory:=memoryEq
    live:=currentLive
    addresses:=currentAddress
    types:=currentTypes
    extras:=currentExtras
    tracked:=trackedEq
    runtime:=helperRuntime
    cache:=helperCache
    borrow:=helperBorrow
    frameOwned:=frameOwned
    clocks:=helperClocks
    body:=helperBody
    location:=location
    size:=sizeDone
    returned:=returned
    argument:=argument
    argumentAt:=argumentAt
    dead2:=dead2
    dead3:=dead3
    dead4:=dead4
    destination:=helperDestination
    continuation:=helperContinuation
    varargs:=helperVarargs
    callerValid:=rootValid
    callerLive:=rootLive
    callerCached:=rootCached
    callerClocks:=callerClocks }⟩

private theorem fetched {frame : CompilerFrameContext.ActualFrame} {index : Nat} {slot : LocalState Provenance LocalLayout}
    (valid : index<frame.locals.size) (eq : frame.locals[index]?=some slot) : frame.locals[index]=slot :=
  Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans eq)

variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    {out : Output limits C count} {ready : CurrentCallResourceBodyReadiness.Ready C} {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
    (result : CurrentCallResourceLenReturn.Result out ready Q stage)

/-- Actual current address data is inherited from the SAME original physical
binding; scalar ownership alone is not used to choose a base address. -/
theorem source_address : ∃ base : UInt64,
    result.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩ ∧
    Q.pointer.value=Pointer.new (.concrete id out.sourceOutput.tag) (Size.ofBytes (base+UInt64.ofNat offset)) ∧
    base+UInt64.ofNat offset≠0 := by
  obtain ⟨base,cached,pointer,nonnull⟩:=CurrentCallResourceSharedStage.source_address out
  have afterAddresses : (CurrentCallResourceSharedStage.afterMachine out ready).user.addresses=(CurrentCallResourceSharedStage.machine out).user.addresses:=rfl
  have addresses:=result.flags.addresses.trans (result.helper.addresses.trans afterAddresses)
  refine ⟨base,?_,?_,nonnull⟩
  · rw [addresses]
    exact cached
  · rw [result.sourcePointer]
    exact pointer

theorem source_pair : result.rootFrame.locals[1]?=some ⟨.live (.immediate
    (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (CurrentCallResourceSourceAfterBool.pointer out).value len ActualReferenceMetadata.reference).imm),some ActualReferenceMetadata.reference⟩ := by
  have pair:=CurrentCallResourceSharedStage.source_pair out result.callerFrame result.shape
  have after:=(CurrentCallResourceLenFacts.other result 1 (by decide) (by decide)).trans pair
  simpa only [CurrentCallTypedSourceCopy.value] using after

private theorem margin (old middle final : Nat) (first : middle≤old+1) (second : final≤middle+1)
    (room : old+6<65536) : final+4<65536 := by omega

include result in
/-- Both actual Len constructors consume only two of the reserved node slots. -/
theorem nodes_margin : (CurrentCallResourceLenReturn.releasedTree out ready).nodes.size+4<65536 := by
  obtain ⟨snapshot⟩:=CurrentCallResourceLenReturn.preStrongSnapshot out ready Q result.sourcePointer result.sourceAllocation stage
  have nonzero : len≠0:=by intro zero;have positive:=C.positive;rw [zero] at positive;contradiction
  have sharedTree : (GeneralBorrowRawSharedExpression.child Q.allocation.extra out.boolOutput.global.protectedTags out.sourceOutput.tag out.boolOutput.global.nextPointerTag
      (UInt64.ofNat offset) len .VisitChildrenOfAccessed).tree=CurrentCallResourceSharedStage.tree out:=by rw [result.sourceAllocation];rfl
  have rows:=stage.rows
  rw [sharedTree] at rows
  change OwnedOn (S05CurrentReadProtectorRelease.Authority (CurrentCallResourceSharedStage.tree out)
    (S05ConcreteProtectedChildCompletion.extend Q.precise.completion stage.reader Q.pointer.grant)
    (CurrentCallResourceLenInvoke.held out ready).global.protectedTags stage.preparation.geometry.selectedRoot Q.pointer.grant stage.reader)
    (UInt64.ofNat offset) (UInt64.ofNat offset+len) (CurrentCallResourceSharedStage.tree out).locations at rows
  have primary : ∀ root,(CurrentCallResourceSharedStage.tree out).roots[0]?=some root →
      Below (S05ConcreteProtectedChildCompletion.extend Q.precise.completion stage.reader Q.pointer.grant) root Q.pointer.grant := by
    intro root slot
    have same : root=allocationRoot:=Option.some.inj (slot.symm.trans snapshot.primarySlot)
    subst root
    exact snapshot.primaryBelow
  obtain ⟨_,_,_,_,_,growth,_⟩:=CurrentCallLenReadEntry.invoke (CurrentCallResourceSharedStage.tree out)
    (S05ConcreteProtectedChildCompletion.extend Q.precise.completion stage.reader Q.pointer.grant)
    (CurrentCallResourceLenInvoke.held out ready).global {} id snapshot.runtime snapshot.parents snapshot.distinct
    stage.preparation.geometry.selectedPosition stage.preparation.geometry.selectedRoot Q.pointer.grant stage.reader snapshot.rootNode snapshot.readerNode
    primary snapshot.rootSlot snapshot.rootAt snapshot.sourcePath snapshot.readerAt snapshot.readerPath
    (CurrentCallResourceLenInvoke.helper_room out ready) (by have m:=snapshot.margin;omega) (by have m:=snapshot.margin;omega)
    (UInt64.ofNat offset) len nonzero rows snapshot.bounds
  have actualTree : (((CurrentCallResourceSharedStage.tree out).performBorrowAccessRange (.concrete snapshot.readerNode.tag)
      (Size.ofBytes (UInt64.ofNat offset)) (Size.ofBytes len) .Read
      (GeneralBorrowFnEntryRegistration.registered (CurrentCallResourceLenInvoke.held out ready).global {} id
        (CurrentCallResourceLenInvoke.helper_room out ready)).1.protectedTags .VisitChildrenOfAccessed).tree.newChild
      (Size.ofBytes (UInt64.ofNat offset)) (.concrete snapshot.readerNode.tag) (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true).tree=CurrentCallResourceLenInvoke.borrowedTree out ready := by
    rw [snapshot.readerTag]
    rfl
  rw [actualTree] at growth
  have frame:=GeneralBorrowStructuralReleaseGeometryFrame.release (CurrentCallResourceLenInvoke.borrowedTree out ready)
    (CurrentCallResourceLenReturn.liveTracker out ready).global.protectedTags (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag
  have releasedNodes : (CurrentCallResourceLenReturn.releasedTree out ready).nodes=(CurrentCallResourceLenInvoke.borrowedTree out ready).nodes:=by
    simpa only [CurrentCallResourceLenReturn.releasedTree] using congrArg BorrowTree.nodes frame
  rw [←releasedNodes] at growth
  have sharedGrowth:=stage.growth
  rw [sharedTree] at sharedGrowth
  have oldSize:=congrArg (fun allocation : Allocation Provenance BorrowTree=>allocation.extra.nodes.size) result.sourceAllocation
  rw [oldSize] at sharedGrowth
  exact margin _ _ _ sharedGrowth growth (CurrentCallResourceBodyReadiness.current_nodes out ready)

theorem counter : (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag.value.toNat=
    out.boolOutput.global.nextPointerTag.value.toNat+2 := by
  have first : (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag.value.toNat=
      out.boolOutput.global.nextPointerTag.value.toNat+1:=
    GenericFunctionEntryNumerics.successor_value out.boolOutput.global.nextPointerTag (CurrentCallResourceBodyReadiness.current_room out ready)
  have second : (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag.value.toNat=
      (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag.value.toNat+1:=
    GenericFunctionEntryNumerics.successor_value (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag (CurrentCallResourceLenInvoke.helper_room out ready)
  omega

theorem tags_margin : (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag.value.toNat+4<18446744073709551615 := by
  have numeric:=counter (out:=out) (ready:=ready)
  have room:=CurrentCallResourceBodyReadiness.current_tags out ready
  omega

/-- The actual accepted guard/preparation reaches the Default-mut statement;
its resource backend and subsequent AsMut call are separate actual steps. -/
theorem accepted_prefix (nonzero : count≠0) (within : count≤len/2) :
    ∃ frame : CompilerFrameContext.ActualFrame,
      (SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] result.rootFrame result.machine)
        (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span
          (RootZeroCompleteState.tick options remaining span result.machine)))) ∧
      (frame.body=result.rootFrame.body ∧ frame.bodyIdentity=result.rootFrame.bodyIdentity ∧
      frame.functionInstance=result.rootFrame.functionInstance ∧ frame.extra=result.rootFrame.extra ∧
      frame.returnPlace=result.rootFrame.returnPlace ∧ frame.returnContinuation=result.rootFrame.returnContinuation ∧
      frame.vaList=result.rootFrame.vaList ∧ frame.localsIdentity=result.rootFrame.localsIdentity ∧frame.trackCallerArg=result.rootFrame.trackCallerArg ∧
      frame.locals.size=25 ∧ frame.location=.mir ⟨6,7⟩ ∧
      frame.locals[1]?=result.rootFrame.locals[1]? ∧ frame.locals[2]?=result.rootFrame.locals[2]? ∧
      frame.locals[15]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      frame.locals[16]?=some ⟨.live (.immediate .uninit),none⟩ ∧ CopyHelperCleanup.AllImmediate frame) ∧
      GenericLenAcceptedPrelude.FrameFacts result.rootFrame frame := by
  have sz:=CurrentCallResourceLenFacts.size result
  have valid (index : Fin 25) : index.val<result.rootFrame.locals.size := by rw [sz];exact index.isLt
  obtain ⟨value,layout,shared⟩:=CurrentCallResourceLenFacts.shared_slot result
  have s12:=fetched (valid ⟨12,by decide⟩) shared
  have s13:=fetched (valid ⟨13,by decide⟩) (CurrentCallResourceLenFacts.slot13 result)
  have s0:=fetched (valid ⟨0,by decide⟩) (CurrentCallResourceLenFacts.zero_slot result)
  have s7:=fetched (valid ⟨7,by decide⟩) (CurrentCallResourceLenFacts.slot7 result)
  have s8:=fetched (valid ⟨8,by decide⟩) (CurrentCallResourceLenFacts.slot8 result)
  have s9:=fetched (valid ⟨9,by decide⟩) (CurrentCallResourceLenFacts.slot9 result)
  have s10:=fetched (valid ⟨10,by decide⟩) (CurrentCallResourceLenFacts.slot10 result)
  have s11:=fetched (valid ⟨11,by decide⟩) (CurrentCallResourceLenFacts.len_slot result)
  have s15:=fetched (valid ⟨15,by decide⟩) (CurrentCallResourceLenFacts.unused result ⟨15,by decide⟩ (by decide) (by decide) (by decide))
  have s16:=fetched (valid ⟨16,by decide⟩) (CurrentCallResourceLenFacts.unused result ⟨16,by decide⟩ (by decide) (by decide) (by decide))
  obtain ⟨body,identity,callee,clocks,rest⟩:=CurrentCallResourceLenFacts.root_metadata result
  have model:=CurrentCallResourceLenFacts.model result
  obtain ⟨tracker,tracked,mode⟩:=model.defaultTracker
  have countPositive : (0 : UInt64)<count := UInt64.lt_iff_toNat_lt.mpr (by
    have notzero : count.toNat≠0:=by intro eq;exact nonzero (UInt64.toNat_inj.mp eq)
    simp only [UInt64.toNat_zero];omega)
  obtain ⟨frame,⟨trace,details⟩,facts⟩ := GenericLenAcceptedPrelude.executes_full options limits remaining span
    (DuplicatePrefixCallModel.sourceComparator options remaining span result.machine model)
    model.debugOff C.validationFuel C.validationEq result.rootFrame result.machine len count countPositive within sz value
    (congrArg LocalState.value s12) (congrArg LocalState.value s13) (congrArg LocalState.layout s13)
    (congrArg LocalState.value s0) (congrArg LocalState.layout s0) (congrArg LocalState.value s7) (congrArg LocalState.layout s7)
    (congrArg LocalState.value s15) (congrArg LocalState.layout s15) (congrArg LocalState.value s16) (congrArg LocalState.layout s16)
    (congrArg LocalState.value s8) (congrArg LocalState.layout s8)
    (congrArg LocalState.value s9) (congrArg LocalState.layout s9)
    (congrArg LocalState.value s10) (congrArg LocalState.layout s10)
    (congrArg LocalState.value s11) (congrArg LocalState.layout s11)
    body identity callee (CurrentCallResourceLenFacts.location result) (CurrentCallResourceLenFacts.immediate result) clocks tracker tracked mode
    model.ghostOff model.shallow model.unchecked model.noGc model.fixedScheduler
  exact ⟨frame,trace,details,facts⟩

/-- Pure actual statement transport; its two status inputs are derived by the Default-mut resource producer. -/
abbrev default_statement := @statement_of_steps

end
end DuplicatePrefix.CurrentCallResourceAsMutCall
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallResourceAsMutCall.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual resource AsMut call dependency {dependency}"
