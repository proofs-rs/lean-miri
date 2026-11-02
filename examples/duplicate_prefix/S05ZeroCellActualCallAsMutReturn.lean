import duplicate_prefix.S05ZeroCellActualCallLenReturn
import duplicate_prefix.PositiveRootMutablePreparation
import duplicate_prefix.GeneralBorrowFreshDefaultChild
import duplicate_prefix.GeneralBorrowForestAcceptedAfterLenCache
import duplicate_prefix.RootReferenceBorrow
import duplicate_prefix.ProtectedReferenceValidator
import duplicate_prefix.ReferenceArgumentCopy
import duplicate_prefix.GenericAsMutCallFrontend
import duplicate_prefix.AsMutCallCore
import duplicate_prefix.AsMutPush
import duplicate_prefix.AsMutTail
import duplicate_prefix.AsMutInstall
import duplicate_prefix.ScopedFrame
import duplicate_prefix.AsMutEntry
import duplicate_prefix.AsMutFinish
import duplicate_prefix.AsMutInitializedShape
import duplicate_prefix.AsMutPtrBody
import duplicate_prefix.AsMutPtrReturn
import Init.Internal.Order.While

namespace DuplicatePrefix.S05ZeroCellActualCallAsMutReturn.PureTree
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open S05ZeroCellJointPacket (sourceId)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

/-- The exact len helper allocator, registration and endCall expressions. -/
def lenHeld : MachineHooks.BorrowState := TypedBorrowSteps.registeredTracker
  (ReferenceBorrowDriver.allocatedTracker S05ZeroCellActualCallLenReturn.PureTree.postSharedTracker
    S05ZeroCellActualCallLenReturn.PureTree.fresh)
  S05ZeroCellActualCallLenReturn.PureTree.tracker.global.nextPointerTag

def loan : FrameState := ({} : FrameState).addProtector sourceId
  S05ZeroCellActualCallLenReturn.PureTree.tracker.global.nextPointerTag

def returnedTracker : MachineHooks.BorrowState := {lenHeld with global := lenHeld.global.endCall loan}
def tree : BorrowTree := S05ZeroCellActualCallLenReturn.PureTree.released.tree
def parent : BorTag := S05ZeroCellActualCallSharedStmt.PureTree.initialGlobal.nextPointerTag

def tracker : MachineHooks.BorrowState := {returnedTracker with retagMode := RootReferenceInfo.mode false}
theorem fresh : tracker.global.nextPointerTag.value < 18446744073709551615 := by decide +kernel

theorem default_initial : RetagPolicy.initialLocationState (RootReferenceInfo.policy false) true =
    .ok (RootReferenceInfo.initial false) := NestedConstruction.mutable_two_phase_initial

def defaultRead := tree.performBorrowAccessRange (.concrete parent) Size.ZERO (Size.ofBytes 2)
  .Read tracker.global.protectedTags .VisitChildrenOfAccessed

def defaultChild := defaultRead.tree.newChild Size.ZERO (.concrete parent) tracker.global.nextPointerTag
  (DedupRangeMap.new (Size.ofBytes 2) (RootReferenceInfo.initial false))
  (RootReferenceInfo.policy false).outsidePermission false

theorem default_read_complete : defaultRead.status = .Completed := by cbv
theorem default_child_complete : defaultChild.outcome = .ok () := by cbv

/-- The rvalue's original mode is restored, retaining the allocator increment. -/
def afterDefaultTracker : MachineHooks.BorrowState :=
  {ReferenceBorrowDriver.allocatedTracker tracker fresh with retagMode := returnedTracker.retagMode}
def helperTracker : MachineHooks.BorrowState := {afterDefaultTracker with retagMode := .FnEntry}
theorem helperFresh : helperTracker.global.nextPointerTag.value < 18446744073709551615 := by decide +kernel

def heldGlobal : GlobalState := TypedBorrowSteps.registeredGlobal
  (ReferenceBorrowDriver.allocatedTracker helperTracker helperFresh) helperTracker.global.nextPointerTag

theorem helper_initial : RetagPolicy.initialLocationState ChildBorrow.fnEntryPolicy true =
    .ok GeneralBorrowFreshChild.inside := ChildBorrow.mutable_fn_entry_initial_location true

def helperRead := defaultChild.tree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag)
  Size.ZERO (Size.ofBytes 2) .Read heldGlobal.protectedTags .VisitChildrenOfAccessed

def helperChild := helperRead.tree.newChild Size.ZERO (.concrete tracker.global.nextPointerTag)
  helperTracker.global.nextPointerTag (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshChild.inside)
  ChildBorrow.fnEntryPolicy.outsidePermission true

theorem helper_read_complete : helperRead.status = .Completed := by cbv
theorem helper_child_complete : helperChild.outcome = .ok () := by cbv

def releaseRead := helperChild.tree.performBorrowAccessRange (.concrete helperTracker.global.nextPointerTag)
  Size.ZERO (Size.ofBytes 2) .Read heldGlobal.protectedTags .SkipChildrenOfAccessed

def released := helperChild.tree.releaseProtector helperTracker.global.nextPointerTag heldGlobal.protectedTags

theorem release_read_complete : releaseRead.status = .Completed := by cbv
theorem release_complete : released.status = .Released := by cbv

theorem actual_release : helperChild.tree.releaseProtector helperTracker.global.nextPointerTag heldGlobal.protectedTags =
    ⟨released.tree,.Released⟩ := by
  change released = ⟨released.tree,.Released⟩
  cases result : released with
  | mk next status =>
    have good : status = .Released := by simpa only [result] using release_complete
    cases good
    rfl

end DuplicatePrefix.S05ZeroCellActualCallAsMutReturn.PureTree

/-! Same actual closed call, from the Len return to the as_mut_ptr return.
New tree calculations are confined to the generated Default mutable reference,
helper argument and release. Existing source guard/call/body/return APIs perform
all execution. The endpoint retains its source frame and machine field facts. -/
namespace DuplicatePrefix.S05ZeroCellActualCallAsMutReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures
open Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess RootReferenceInfo RootReferenceTrees
open S05ZeroCellActualCallParameters S05ZeroCellJointPacket
open AsMutUncachedCall RootZeroCompleteState
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option linter.unusedSimpArgs false
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

private def defaultRead (tree : BorrowTree) (protections : ProtectedTags) (parentTag : BorTag)
    (offset len : UInt64) (mode : Tree.ChildrenVisitMode) :=
  tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len) .Read protections mode
private def defaultChild (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (offset len : UInt64) (mode : Tree.ChildrenVisitMode) :=
  (defaultRead tree protections parentTag offset len mode).tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
/-- Actual TwoPhase mutable Ref from the exact len-return source tree.
All borrow completion facts are derived internally; physical local/compiler facts remain explicit. -/
private theorem default_rvalue
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
    (treeEq : entry.allocation.extra = PureTree.tree)
    (parentEq : parentTag = PureTree.parent)
    (nextEq : tracker.global.nextPointerTag = PureTree.tracker.global.nextPointerTag)
    (protectedEq : tracker.global.protectedTags = PureTree.tracker.global.protectedTags)
    (offsetEq : offset = 0) (lenEq : len = 2)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (localId : MIR.LocalId) (destination16 : localId = 16)
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
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let inner := config options remaining span
    let value := RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout false)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry (defaultChild entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Ref region (RootReferenceRvalue.borrowKind false) ⟨1,#[.Deref]⟩) ⟨localId,#[]⟩ (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (ActualLocalCopy.written frame localId (layout false) validDest value.imm) resultMachine) := by
  have different : localId ≠ 1 := by rw [destination16]; decide
  let inner := config options remaining span
  let outer := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks outer limits
  let cachedFrame := LocalPlaces.cachePlaceLayout frame localId (layout false) validDest
  let activeTracker := {tracker with retagMode := mode false}
  let enteredMachine := RootReferenceRvalue.enter machine tracker false
  let updatedMachine := {ReferenceBorrowDriver.allocatedMachine enteredMachine activeTracker fresh with
    memory := RetagEntry.updatedMemory machine.memory id entry (defaultChild entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
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
  have run : (defaultRead entry.allocation.extra tracker.global.protectedTags parentTag offset len .VisitChildrenOfAccessed).status = .Completed ∧
      (defaultRead entry.allocation.extra tracker.global.protectedTags parentTag offset len .VisitChildrenOfAccessed).tree = PureTree.defaultRead.tree := by
    simpa only [defaultRead,treeEq,parentEq,offsetEq,lenEq,protectedEq,PureTree.defaultRead,Miri.ABI.Size.ZERO,Miri.ABI.Size.ofBytes] using And.intro PureTree.default_read_complete (Eq.refl PureTree.defaultRead.tree)
  let parentTree := (defaultRead entry.allocation.extra tracker.global.protectedTags parentTag offset len .VisitChildrenOfAccessed).tree
  let resultTree := (defaultChild entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree
  have readTree : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read activeTracker.global.protectedTags .VisitChildrenOfAccessed).tree = parentTree := rfl
  have readDone : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read activeTracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := run.1
  have defaultChild' : parentTree.newChild (Size.ofBytes offset) (.concrete parentTag) activeTracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) (initial false)) (policy false).outsidePermission false =
      ⟨resultTree,.ok ()⟩ := by
    have succeeded : (defaultChild entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).outcome = .ok () := by
      unfold defaultChild
      rw [run.2]
      simpa [parentEq,nextEq,offsetEq,lenEq,
        PureTree.defaultChild,RootReferenceInfo.initial,RootReferenceInfo.policy,NestedConstruction.twoPhasePolicy,
        NestedConstruction.mutableRead,GeneralBorrowFreshDefaultChild.inside,Miri.ABI.Size.ZERO,Miri.ABI.Size.ofBytes] using PureTree.default_child_complete
    exact GeneralBorrowFreshReborrowStages.child_complete _ succeeded
  have writer := RootReferenceWrite.positive_cached options limits remaining span ctx debugOff cmp false dynamicFuel validityFuel
    fuelEq validationFuel id entry base offset len parentTag positive nonzero signedFits bounds
    frames cachedFrame enteredMachine activeTracker entered current fresh localId .uninit cachedDestValid destinationLive destinationCached
    noClocks ghost shallow cachedAddress present race parentTree (defaultChild entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree
    readTree readDone defaultChild' metadata notConstructed
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

private theorem default_step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (ctx : ActualReferenceContext.Context options remaining span) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (debug : options.place.debugAssertions=false) (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (size : frame.locals.size=25)
    (temp12 : Immediate Provenance)
    (live12 : (frame.locals[12]'(by omega)).value=.live (.immediate temp12))
    (live13 : (frame.locals[13]'(by omega)).value=.live (.immediate .uninit)) (cache13 : (frame.locals[13]'(by omega)).layout=none)
    (live0 : (frame.locals[0]'(by omega)).value=.live (.immediate .uninit)) (cache0 : (frame.locals[0]'(by omega)).layout=none)
    (live7 : (frame.locals[7]'(by omega)).value=.live (.immediate .uninit))
    (cache7 : (frame.locals[7]'(by omega)).layout=none)
    (dead15 : (frame.locals[15]'(by omega)).value=.dead) (cache15 : (frame.locals[15]'(by omega)).layout=none)
    (dead16 : (frame.locals[16]'(by omega)).value=.dead) (cache16 : (frame.locals[16]'(by omega)).layout=none)
    (live8 : (frame.locals[8]'(by omega)).value=.live (.immediate .uninit)) (cache8 : (frame.locals[8]'(by omega)).layout=none)
    (live9 : (frame.locals[9]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 1)))))
    (cache9 : (frame.locals[9]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (live10 : (frame.locals[10]'(by omega)).value=.live (.immediate .uninit)) (cache10 : (frame.locals[10]'(by omega)).layout=none)
    (live11 : (frame.locals[11]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 2)))))
    (cache11 : (frame.locals[11]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨3,0⟩)
    (all : CopyHelperCleanup.AllImmediate frame) (noClocks : frame.extra.dataRace=none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker) (mode : tracker.retagMode=.Default)
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (base : UInt64) (nonzero : base ≠ 0)
    (bounds : 2 ≤ entry.allocation.byteSize.bytes.toNat)
    (treeEq : entry.allocation.extra = PureTree.tree)
    (nextEq : tracker.global.nextPointerTag = PureTree.tracker.global.nextPointerTag)
    (protectedEq : tracker.global.protectedTags = PureTree.tracker.global.protectedTags)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (source1 : frame.locals[1]? = some ⟨.live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new (.concrete id (PureTree.parent)) (Size.ofBytes base))
      2 ActualReferenceMetadata.reference).imm),some ActualReferenceMetadata.reference⟩) :
    let m2 := tick options remaining span (tick options remaining span machine)
    let room : tracker.global.nextPointerTag.value < 18446744073709551615 := by rw [nextEq];decide
    let value := RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes base)) 2 (RootReferenceInfo.layout false)
    let post := {ReferenceBorrowDriver.allocatedMachine m2 tracker room with
      memory := RetagEntry.updatedMemory m2.memory id entry PureTree.defaultChild.tree}
    ∃ prepared : CompilerFrameContext.ActualFrame, ∃ valid16 : 16 < prepared.locals.size,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits (Storage.withCurrent #[] frame machine)
        (Storage.withCurrent #[] (CopyHelperSteps.advance
          (ActualLocalCopy.written prepared 16 (RootReferenceInfo.layout false) valid16 value.imm) ⟨6,7⟩) post) ∧
      prepared.body = frame.body ∧ prepared.bodyIdentity = frame.bodyIdentity ∧ prepared.functionInstance = frame.functionInstance ∧
      prepared.extra = frame.extra ∧ prepared.returnPlace = frame.returnPlace ∧ prepared.returnContinuation = frame.returnContinuation ∧
      prepared.vaList = frame.vaList ∧ prepared.localsIdentity = frame.localsIdentity ∧ prepared.trackCallerArg = frame.trackCallerArg ∧
      prepared.locals.size = 25 ∧ prepared.location = .mir ⟨6,7⟩ ∧ prepared.locals[1]? = frame.locals[1]? ∧
      prepared.locals[15]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      prepared.locals[2]? = frame.locals[2]? ∧
      (∀ index,17 ≤ index → prepared.locals[index]? = frame.locals[index]?) ∧
      prepared.locals[0]? = frame.locals[0]? ∧
      CopyHelperCleanup.AllImmediate prepared := by
  obtain ⟨prepared,pureTrace,pbody,pidentity,pcallee,pextra,preturn,pcontinuation,pva,plocalsId,ptrack,psize,plocation,
    p0,p1,p2,p13,p15,p16,pkeep,pall⟩ := PositiveRootMutablePreparation.executes options limits remaining span source debug fuel fuelEq
    frame machine 2 1 (by decide) size temp12 live12 live13 cache13 live0 cache0 live7 cache7 dead15 cache15 dead16 cache16
    live8 cache8 live9 cache9 live10 cache10 live11 cache11 body identity callee location all noClocks tracker tracked mode ghost shallow unchecked noGc fixed
  let m2 := tick options remaining span (tick options remaining span machine)
  have fields : m2.memory = machine.memory ∧ m2.borrowTracker = machine.borrowTracker ∧ m2.dataRace = machine.dataRace ∧
      m2.user.addresses = machine.user.addresses ∧ m2.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      m2.user.payload.ghost = machine.user.payload.ghost ∧ m2.user.payload.validation = machine.user.payload.validation := by
    unfold m2 tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have v1 : 1 < prepared.locals.size := by rw [psize];decide
  have v16 : 16 < prepared.locals.size := by rw [psize];decide
  have src := Option.some.inj ((Array.getElem?_eq_getElem v1).symm.trans (p1.trans source1))
  have dst := Option.some.inj ((Array.getElem?_eq_getElem v16).symm.trans p16)
  have srcLive : prepared.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id (PureTree.parent)) (Size.ofBytes (base+0))) 2 ActualReferenceMetadata.reference).imm) := by
    rw [src]
    simp only [UInt64.add_zero]
    rw [CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span,CanonicalConfigFacts.actual_access_runtime options () remaining span]
  have room : tracker.global.nextPointerTag.value < 18446744073709551615 := by rw [nextEq];decide
  have query := RootReferenceFacts.compute_destination #[] prepared m2 (pbody.trans body) (pidentity.trans identity) (pcallee.trans callee) false
  have expression := default_rvalue options limits remaining span ctx debug cmp .Erased dynamicFuel fuel dynamicEq fuelEq
    base 0 2 id entry (by decide) (by simpa using nonzero) (by decide) #[] prepared m2 tracker (fields.2.1.trans tracked) mode room
    (PureTree.parent) treeEq rfl nextEq protectedEq rfl rfl (by simpa using bounds) 16 rfl v1 v16 srcLive
    (by rw [src]) (by rw [dst]) (by rw [dst]) query (by rw [pextra];exact noClocks)
    (fields.2.2.2.2.2.1.trans ghost) (fields.2.2.2.2.2.2.trans shallow)
    (by rw [fields.2.2.2.1];exact cachedAddress) (by rw [fields.1];exact present) (fields.2.2.1.trans race)
    (by change m2.user.payload.payload.user.types.metadata = _;rw [fields.2.2.2.2.1];exact metadata)
    (by change m2.user.payload.payload.user.types.entries.any _ = _;rw [fields.2.2.2.2.1];exact notConstructed)
  have treeDone : (defaultChild entry.allocation.extra tracker.global.protectedTags
      (PureTree.parent) tracker.global.nextPointerTag 0 2 .VisitChildrenOfAccessed).tree = PureTree.defaultChild.tree := by
    unfold defaultChild defaultRead
    simp only [treeEq,protectedEq,nextEq,PureTree.defaultChild,PureTree.defaultRead]
    rfl
  let value := RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes base)) 2 (RootReferenceInfo.layout false)
  let post := {ReferenceBorrowDriver.allocatedMachine m2 tracker room with memory := RetagEntry.updatedMemory m2.memory id entry PureTree.defaultChild.tree}
  let written := ActualLocalCopy.written prepared 16 (RootReferenceInfo.layout false) v16 value.imm
  have effect : evalRvalueIntoPlace (ExecutionMachine.rvalueHooks (config options (remaining+1) span) limits) ()
      (.Ref .Erased (RootReferenceRvalue.borrowKind false) ⟨1,#[.Deref]⟩) ⟨16,#[]⟩ (Storage.withCurrent #[] prepared m2) =
      .ok () (Storage.withCurrent #[] written post) := by
    simpa only [treeDone,UInt64.add_zero,written,value,post] using expression
  have step := CopyHelperSteps.assign_of_actual_rvalue (config options (remaining+1) span) limits #[] prepared written m2 post
    ⟨6,7⟩ ⟨16,#[]⟩ (.Ref .Erased (RootReferenceRvalue.borrowKind false) ⟨1,#[.Deref]⟩) plocation
    (by simpa only [written,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using plocation)
    (by rw [pbody,body];exact RootReferenceFacts.statement false) effect
  exact ⟨prepared,v16,SuccessfulTrace.append pureTrace (.next step (.refl _)),pbody,pidentity,pcallee,pextra,preturn,pcontinuation,pva,plocalsId,ptrack,psize,plocation,p1,p15,p2,pkeep,p0,pall⟩

private def helperTree (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag) (offset len : UInt64) :=
  let registered := TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag
  let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered.protectedTags .VisitChildrenOfAccessed
  (read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree

/-- Actual diagnostic as_mut_ptr argument installation; every borrow completion is internal. -/
private theorem install_data
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (exprTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (treeEq : entry.allocation.extra = PureTree.defaultChild.tree)
    (parentEq : exprTag = PureTree.tracker.global.nextPointerTag)
    (nextEq : tracker.global.nextPointerTag = PureTree.helperTracker.global.nextPointerTag)
    (protectedEq : tracker.global.protectedTags = PureTree.helperTracker.global.protectedTags)
    (offsetEq : offset = 0) (lenEq : len = 2)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (valid : 1 < frame.locals.size)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
    (uncached : frame.locals[1].layout = none) (dead : frame.locals[1].value = .dead)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let output := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let finalTree := helperTree entry.allocation.extra tracker exprTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    AsMutInstall.action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) value
      (Storage.withCurrent frames frame machine) =
      .ok (1,1) (Storage.withCurrent frames
        (AsMutInstall.resultFrame frame valid value output borrowFrame id tracker.global.nextPointerTag) resultMachine) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (Provenance.concrete id exprTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let cache := AsMutInstall.cacheFrame frame valid
  have cacheValid : 1 < cache.locals.size := by simpa [cache,AsMutInstall.cacheFrame,AsMutInstall.spanFrame,LocalOperands.cachedLayoutFrame] using valid
  let live := RootArgumentEntry.liveFrame cache 1 cacheValid
  have liveValid : 1 < live.locals.size := by simpa [live,RootArgumentEntry.liveFrame] using cacheValid
  have cached : live.locals[1].layout = some ActualReferenceMetadata.reference := by
    simp [live,RootArgumentEntry.liveFrame,cache,AsMutInstall.cacheFrame,LocalOperands.cachedLayoutFrame]
  let copied := AsMutPtrArgumentCopy.copiedFrame live 1 value liveValid
  have postValid : 1 < copied.locals.size := by simpa [copied,AsMutPtrArgumentCopy.copiedFrame] using liveValid
  have postLive : copied.locals[1].value = .live (.immediate value) := by simp [copied,AsMutPtrArgumentCopy.copiedFrame]
  have postCached : copied.locals[1].layout = some ActualReferenceMetadata.reference := by
    simpa [copied,AsMutPtrArgumentCopy.copiedFrame] using cached
  let read := entry.allocation.extra.performBorrowAccessRange (.concrete exprTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed
  let child := read.tree.newChild (Size.ofBytes offset) (.concrete exprTag) tracker.global.nextPointerTag
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
  have readFacts : read.status = .Completed ∧ read.tree = PureTree.helperRead.tree := by
    simpa only [read,treeEq,parentEq,nextEq,offsetEq,lenEq,protectedEq,TypedBorrowSteps.registeredGlobal,
      PureTree.helperRead,PureTree.heldGlobal,ReferenceBorrowDriver.allocatedTracker,TypedRetagGeneric.allocatedGlobal,Size.ZERO,Size.ofBytes] using And.intro PureTree.helper_read_complete (Eq.refl PureTree.helperRead.tree)
  have childDone : child.outcome = .ok () := by
    dsimp only [child]
    rw [readFacts.2]
    simpa only [parentEq,nextEq,offsetEq,lenEq,PureTree.helperChild,ChildBorrow.fnEntryPolicy,Size.ZERO,Size.ofBytes] using PureTree.helper_child_complete
  have childComplete := GeneralBorrowFreshReborrowStages.child_complete child childDone
  have info := RootReferenceInfo.facts options remaining span ctx false
  have validated := ProtectedReferenceValidator.positive options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    ActualReferenceMetadata.reference .Mut .FnEntry ChildBorrow.fnEntryPolicy GeneralBorrowFreshChild.inside
    rfl (by decide +kernel) (ChildBorrow.mutable_fn_entry_initial_location true) (by decide +kernel)
    info.shape info.pointeeQuery info.unpin info.unsafeUnpin info.frozen info.dereference
    info.sized info.readable "&mut [u8]" info.named info.classified
    id entry base offset len exprTag positive nonzero signedFits bounds frames copied machine tracker enabled mode
    borrowFrame frameBorrow fresh 1 postValid postLive postCached ghost shallow cachedAddress present race read.tree child.tree
    rfl readFacts.1 childComplete metadata notConstructed
  have checked := ReferenceArgumentCopy.copy_with_nested_validation options limits remaining span debugOff frames live machine
    1 .uninit value liveValid (by simp [live,RootArgumentEntry.liveFrame]) cached noClocks ghost shallow
    (LocalPlaces.localRuntimePlace frames.size live 1 ActualReferenceMetadata.reference).stackView rfl _
    (by rw [validationEq]; exact validated)
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  have typed : cache.body.locals[1]? = some 3 := by change frame.body.locals[1]? = some 3; rw [body]; rfl
  have storage := CallEntryLocals.storage_live options limits (remaining+1) span frames cache machine 1 3 cacheValid
    typed AsMutArgument.reference_storage_trivial (by simpa [cache,AsMutInstall.cacheFrame,AsMutInstall.spanFrame,LocalOperands.cachedLayoutFrame] using dead) noClocks
  have evaluate := CallEntryLocals.destination_cached options limits (remaining+1) span debugOff frames live machine 1
    ActualReferenceMetadata.reference liveValid cached ActualReferenceMetadata.reference_sized
  have compat : h.checkArgumentCompat () (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret)
      (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret)
      (Storage.withCurrent frames cache machine) = .ok true (Storage.withCurrent frames cache machine) := by
    change (config options (remaining+1) span).calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).callCompiler]
    exact AsMutEntryFacts.argument_compat _ options.compatibilityBudget _
  have passed := CallArgumentStages.copy_argument h () ⟨.immediate value,ActualReferenceMetadata.reference⟩
    (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret)
    (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret) 0 ⟨1,#[]⟩ 3
    (Storage.withCurrent frames cache machine) _ _ _ _
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) compat rfl rfl storage evaluate checked
  have query := AsMutLocalStages.span1 options limits (remaining+1) span frames frame machine body identity callee
  have setspan := CallEntryLocals.set_span options limits (remaining+1) span frames frame machine ⟨613⟩
  change AsMutCallCore.spanAt h ⟨613⟩ (Storage.withCurrent frames frame machine) = _ at setspan
  have layout := AsMutLocalStages.layout1 options limits (remaining+1) span frames (AsMutInstall.spanFrame frame) machine
    body identity callee valid uncached
  dsimp only [AsMutInstall.spanFrame] at layout
  dsimp only [cache,AsMutInstall.cacheFrame,AsMutInstall.spanFrame] at passed
  unfold AsMutInstall.action
  simp only [bind,EStateM.bind]
  rw [query]
  dsimp only
  rw [setspan]
  dsimp only
  rw [layout]
  dsimp only
  rw [ActualReferenceMetadata.reference_ty]
  rw [passed]
  simp only [pure,Pure.pure,EStateM.pure]
  congr 1


private theorem scoped_install_data
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (exprTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (treeEq : entry.allocation.extra = PureTree.defaultChild.tree)
    (parentEq : exprTag = PureTree.tracker.global.nextPointerTag)
    (nextEq : tracker.global.nextPointerTag = PureTree.helperTracker.global.nextPointerTag)
    (protectedEq : tracker.global.protectedTags = PureTree.helperTracker.global.protectedTags)
    (offsetEq : offset = 0) (lenEq : len = 2)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (valid : 1 < frame.locals.size)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
    (uncached : frame.locals[1].layout = none) (dead : frame.locals[1].value = .dead)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let output := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let finalTree := helperTree entry.allocation.extra tracker exprTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (AsMutInstall.action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) value)
      (Storage.withCurrent frames frame machine) =
      .ok (1,1) (Storage.withCurrent frames
        (AsMutInstall.resultFrame frame valid value output borrowFrame id tracker.global.nextPointerTag) resultMachine) := by
  let activeTracker := {tracker with retagMode := .FnEntry}
  let activeMachine := {machine with borrowTracker := some activeTracker}
  have made := install_data options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len exprTag positive nonzero signedFits frames frame activeMachine
    activeTracker rfl rfl borrowFrame frameBorrow fresh treeEq parentEq nextEq protectedEq offsetEq lenEq bounds valid body identity callee uncached dead noClocks ghost shallow
    cachedAddress present race metadata notConstructed
  change MachineHooks.withRetagMode .FnEntry _ _ = _
  unfold MachineHooks.withRetagMode
  simp only [Storage.withCurrent]
  rw [enabled]
  dsimp only
  simp only [Storage.withCurrent,activeMachine,activeTracker] at made
  rw [made]
  simp only [Storage.withCurrent,TypedBorrowSteps.registeredMachine,ReferenceBorrowDriver.allocatedMachine,
    ReferenceBorrowDriver.allocatedTracker,TypedBorrowSteps.registeredGlobal,activeMachine,activeTracker]
  rfl

private theorem as_mut_call
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (treeEq : entry.allocation.extra = PureTree.defaultChild.tree)
    (parentEq : parentTag = PureTree.tracker.global.nextPointerTag)
    (offsetEq : offset = 0) (lenEq : len = 2)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (nextEq : tracker.global.nextPointerTag = PureTree.helperTracker.global.nextPointerTag)
    (protectedEq : tracker.global.protectedTags = PureTree.helperTracker.global.protectedTags)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (body : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨6,8⟩)
    (source : PreparedContracts.SourceComparator)
    (valid16 : (16 : MIR.LocalId) < caller.locals.size)
    (value16 : caller.locals[16].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))
      len ActualReferenceMetadata.reference).imm))
    (cached16 : caller.locals[16].layout = some ActualReferenceMetadata.reference)
    (destValid : 15 < caller.locals.size) (old : Immediate Provenance)
    (destLive : caller.locals[15].value = .live (.immediate old))
    (uncached : caller.locals[15].layout = none)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) caller machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) caller machine)).entries.any (·.value.ty == 4) = false)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) (cachedCaller caller destValid) machine)
      (LocalPlaces.localRuntimePlace (#[] : Array CompilerFrameContext.ActualFrame).size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) (cachedCaller caller destValid) machine)
      (LocalPlaces.localRuntimePlace (#[] : Array CompilerFrameContext.ActualFrame).size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current) :
    let cfg := config options remaining span
    let initial := Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) caller machine
    let before := Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) (cachedCaller caller destValid) machine
    let destination := (LocalPlaces.localRuntimePlace (#[] : Array CompilerFrameContext.ActualFrame).size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
    let finalTree := helperTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    (Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody HelperCompilerFacts.asMutPtrAbi
      #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩] false destination (.goto (some 7) .Continue) before =
      .ok () (Storage.withCurrent #[cachedCaller caller destValid]
        (AsMutEntry.initialized options before destination value adjusted id tracker.global.nextPointerTag) resultMachine)) ∧
    Call.evalCallTerminator (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      () limits.callDispatch AsMutEvaluateCall.terminator initial =
      .ok () (Storage.withCurrent ((#[] : Array CompilerFrameContext.ActualFrame).push (cachedCaller caller destValid))
        (AsMutEntry.initialized options before destination value adjusted id tracker.global.nextPointerTag) resultMachine) := by
  let frames : Array CompilerFrameContext.ActualFrame := #[]
  let cf := cachedCaller caller destValid
  let before := Storage.withCurrent frames cf machine
  let destination := (LocalPlaces.localRuntimePlace frames.size cf 15 CopyCompilerFacts.destPointerLayout).stackView
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let frame := AsMutEntry.rawFrame options before destination
  let post := (AsMutPush.completed options.userRelevantCrates before destination current).machine
  let result := AsMutInstall.resultFrame frame (by rw [AsMutEntry.raw_size];decide) value adjusted {} id tracker.global.nextPointerTag
  let finalTree := helperTree entry.allocation.extra tracker parentTag offset len
  let afterMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine post tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory post.memory id entry finalTree}
  have valid15 : 15 < cf.locals.size := by simpa [cf,cachedCaller,LocalPlaces.cachePlaceLayout] using destValid
  have live15 : cf.locals[15].value = .live (.immediate old) := by
    simpa [cf,cachedCaller,LocalPlaces.cachePlaceLayout] using destLive
  have cache15 : cf.locals[15].layout = some CopyCompilerFacts.destPointerLayout := by
    simp [cf,cachedCaller,LocalPlaces.cachePlaceLayout]
  have installed : (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (AsMutInstall.action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) value)
      (Storage.withCurrent (frames.push cf) frame post) = .ok (1,1) (Storage.withCurrent (frames.push cf) result afterMachine) := by
    have tracked : post.borrowTracker = some tracker := by
      simp only [post,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,before,Storage.withCurrent,GenericPushRelevance.afterPush]
      split <;> exact enabled
    have fg : frame.extra.borrowTracker = some ({} : FrameState) := by
      simp [frame,AsMutEntry.rawFrame,AsMutFrame.rawFrame,AsMutPush.fresh,CallEntryFacts.freshRoot,before,Storage.withCurrent,enabled]
    have fc : frame.extra.dataRace = none := by
      simp [frame,AsMutEntry.rawFrame,AsMutFrame.rawFrame,AsMutPush.fresh,CallEntryFacts.freshRoot,before,Storage.withCurrent,race]
    apply scoped_install_data options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id entry base offset len parentTag positive nonzero signedFits (frames.push cf) frame post tracker tracked {} fg fresh
      treeEq parentEq nextEq protectedEq offsetEq lenEq bounds (by rw [AsMutEntry.raw_size];decide) rfl rfl rfl rfl rfl fc
    all_goals
      simp only [post,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,before,Storage.withCurrent,GenericPushRelevance.afterPush]
      split
      all_goals first | exact ghost | exact shallow | exact cachedAddress | exact present | exact race | exact metadata | exact notConstructed
  have resultSize : result.locals.size = 5 := by
    simpa only [result,AsMutInstall.resultFrame,AsMutInstall.cacheFrame,AsMutInstall.spanFrame,LocalOperands.cachedLayoutFrame,
      RootArgumentEntry.liveFrame,AsMutPtrArgumentCopy.copiedFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,Array.size_set]
      using AsMutEntry.raw_size options before destination
  have resultDead : result.locals[0].value = .dead := by
    simp [result,AsMutInstall.resultFrame,AsMutInstall.cacheFrame,AsMutInstall.spanFrame,LocalOperands.cachedLayoutFrame,
      RootArgumentEntry.liveFrame,AsMutPtrArgumentCopy.copiedFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,
      frame,AsMutEntry.rawFrame,AsMutFrame.rawFrame,Frame.create]
    with_unfolding_all rfl
  have resultClocks : result.extra.dataRace = none := by
    simp [result,AsMutInstall.resultFrame,AsMutInstall.cacheFrame,AsMutInstall.spanFrame,LocalOperands.cachedLayoutFrame,
      RootArgumentEntry.liveFrame,AsMutPtrArgumentCopy.copiedFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,
      frame,AsMutEntry.rawFrame,AsMutFrame.rawFrame,AsMutPush.fresh,CallEntryFacts.freshRoot,before,Storage.withCurrent,race]
  have tail : AsMutTail.action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      value ⟨.immediate old,CopyCompilerFacts.destPointerLayout⟩ (Storage.withCurrent (frames.push cf) frame post) =
      .ok () (Storage.withCurrent (frames.push cf) (AsMutEntry.initialized options before destination value adjusted id tracker.global.nextPointerTag) afterMachine) := by
    have getframe := CallEntryLocals.get_frame options limits (remaining+1) span (frames.push cf) frame post
    have setframe := CallEntryLocals.set_frame options limits (remaining+1) span (frames.push cf) frame frame post
    have finished := AsMutFinish.finish options limits (remaining+1) span (frames.push cf) result afterMachine AsMutEntryFacts.asMutPreamble
      rfl rfl rfl (by rw [resultSize];decide) resultDead resultClocks
    unfold AsMutTail.action
    simp only [bind,EStateM.bind]
    rw [getframe]
    dsimp only
    have loc : frame.location = .unwinding AsMutEntryFacts.asMutPreamble := by rfl
    rw [loc]
    simp only [pure,Pure.pure,EStateM.pure,EStateM.bind]
    have same : {frame with trackCallerArg := none} = frame := by rfl
    rw [←loc,same,setframe]
    dsimp only
    rw [installed]
    exact finished
  have entryDone : Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody HelperCompilerFacts.asMutPtrAbi
      #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩] false destination (.goto (some 7) .Continue) before =
      .ok () (Storage.withCurrent (frames.push cf) (AsMutEntry.initialized options before destination value adjusted id tracker.global.nextPointerTag) afterMachine) := by
    have read := CallLocalRead.place_to_op_cached options limits (remaining+1) span debugOff frames cf machine 15
      CopyCompilerFacts.destPointerLayout old valid15 live15 cache15 (by decide +kernel) callerClocks ghost
    have pushed := AsMutPush.actual_push options () (remaining+1) span before destination thread index current active top topPresent
    rw [AsMutCallCore.actual_entry_eq,AsMutTail.core_eq]
    simp only [bind,EStateM.bind]
    rw [read]
    dsimp only
    have actualPush : (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).pushRaw ()
        HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody destination (.goto (some 7) .Continue) before =
        .ok () (AsMutPush.completed options.userRelevantCrates before destination current) := by
      change CallMachine.pushRaw (PreparedContracts.actualConfig options () (remaining+1) span).lifecycle
        (PreparedContracts.actualConfig options () (remaining+1) span).compiler.debugAssertions
        HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody destination (.goto (some 7) .Continue) before = _
      rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).debug,debugOff]
      exact pushed
    rw [actualPush]
    exact tail
  refine ⟨entryDone,?_⟩
  exact GenericAsMutCallFrontend.call_uncached options limits remaining budget dispatchFuel span debugOff source cmp
    caller _ machine afterMachine value body identity callee located valid16 value16 cached16 destValid old destLive uncached
    callerClocks ghost backend race entryDone


private theorem direct_of_slots (frame : CompilerFrameContext.ActualFrame) (size : frame.locals.size = 5)
    (value0 value1 : Immediate Provenance)
    (zero : frame.locals[0]?.map (·.value) = some (.live (.immediate value0)))
    (one : frame.locals[1]?.map (·.value) = some (.live (.immediate value1)))
    (two : frame.locals[2]?.map (·.value) = some .dead)
    (three : frame.locals[3]?.map (·.value) = some .dead)
    (four : frame.locals[4]?.map (·.value) = some .dead) :
    ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory) := by
  intro slot member memory
  obtain ⟨i,valid,equal⟩ := Array.mem_iff_getElem.mp member
  subst slot
  have upper : i < 5 := by omega
  have known : frame.locals[i]?.map (·.value) = some (frame.locals[i].value) := by simp only [Array.getElem?_eq_getElem valid,Option.map_some]
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl <;> simp_all

/-- Actual source call step and ten helper MIR statements, with the exact computed
machine retained for subsequent protector release and Return. -/
private theorem before_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (treeEq : entry.allocation.extra = PureTree.defaultChild.tree)
    (parentEq : parentTag = PureTree.tracker.global.nextPointerTag)
    (offsetEq : offset = 0) (lenEq : len = 2)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (nextEq : tracker.global.nextPointerTag = PureTree.helperTracker.global.nextPointerTag)
    (protectedEq : tracker.global.protectedTags = PureTree.helperTracker.global.protectedTags)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (body : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨6,8⟩)
    (source : PreparedContracts.SourceComparator)
    (valid16 : (16 : MIR.LocalId) < caller.locals.size)
    (value16 : caller.locals[16].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))
      len ActualReferenceMetadata.reference).imm))
    (cached16 : caller.locals[16].layout = some ActualReferenceMetadata.reference)
    (destValid : 15 < caller.locals.size) (old : Immediate Provenance)
    (destLive : caller.locals[15].value = .live (.immediate old))
    (uncached : caller.locals[15].layout = none)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) caller machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) caller machine)).entries.any (·.value.ty == 4) = false)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) (cachedCaller caller destValid) machine)
      (LocalPlaces.localRuntimePlace (#[] : Array CompilerFrameContext.ActualFrame).size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) (cachedCaller caller destValid) machine)
      (LocalPlaces.localRuntimePlace (#[] : Array CompilerFrameContext.ActualFrame).size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (machineEq : machine = AsMutPtrReturn.accountedMachine options remaining span beforeMachine)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true) :
    let cfg := config options remaining span
    let before := Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) (cachedCaller caller destValid) machine
    let destination := (LocalPlaces.localRuntimePlace (#[] : Array CompilerFrameContext.ActualFrame).size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
    let finalTree := helperTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    let frame := AsMutEntry.initialized options before destination value adjusted id tracker.global.nextPointerTag
    ∃ done : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] caller beforeMachine)
        (Storage.withCurrent #[cachedCaller caller destValid] done resultMachine) ∧
      done.body = HelperCompilerFacts.asMutPtrBody.body ∧ done.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity ∧
      done.functionInstance = HelperCompilerFacts.asMutPtrCall.callee ∧ done.locals.size = 5 ∧ done.location = .mir ⟨0,10⟩ ∧
      done.locals[0]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer
        (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)))))),some CopyCompilerFacts.destPointerLayout⟩ ∧
      done.locals[1]? = frame.locals[1]? ∧
      done.locals[2]?.map (·.value) = some .dead ∧ done.locals[3]?.map (·.value) = some .dead ∧ done.locals[4]?.map (·.value) = some .dead ∧
      done.extra = frame.extra ∧ done.extra.borrowTracker = some (({} : FrameState).addProtector id tracker.global.nextPointerTag) ∧
      done.extra.dataRace = none ∧ done.returnPlace = destination ∧ done.returnContinuation = .goto (some 7) .Continue ∧ done.vaList = #[] ∧
      (∀ slot ∈ done.locals, ∀ memory, slot.value ≠ .live (.indirect memory)) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let cf := cachedCaller caller destValid
  let before := Storage.withCurrent #[] cf machine
  let destination := (LocalPlaces.localRuntimePlace 0 cf 15 CopyCompilerFacts.destPointerLayout).stackView
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let pointer : Pointer Provenance := Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base pointer len ActualReferenceMetadata.reference).imm
  let post := (AsMutPush.completed options.userRelevantCrates before destination current).machine
  let finalTree := helperTree entry.allocation.extra tracker parentTag offset len
  let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine post tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory post.memory id entry finalTree}
  let frame := AsMutEntry.initialized options before destination value adjusted id tracker.global.nextPointerTag
  have call := as_mut_call options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len parentTag treeEq parentEq offsetEq lenEq positive nonzero signedFits bounds caller machine tracker enabled nextEq protectedEq fresh
    body identity callee located source valid16 value16 cached16 destValid old destLive uncached callerClocks ghost shallow cachedAddress present race backend
    metadata notConstructed thread index current active top topPresent
  have accounting := SourceControl.before_terminator cfg limits () (Storage.withCurrent #[] caller beforeMachine)
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have accounting' : (ExecutionMachine.stepHooks cfg limits).beforeTerminator () (Storage.withCurrent #[] caller beforeMachine) =
      (Storage.withCurrent #[] caller machine,.ok ()) := by
    simpa only [machineEq,AsMutPtrReturn.accountedMachine,SourceControl.accounted,Storage.withCurrent,cfg] using accounting
  have entered : ExecutionMachine.step cfg limits () (Storage.withCurrent #[] caller beforeMachine) =
      (Storage.withCurrent #[cf] frame resultMachine,.ok true) := by
    let block := RootBody.reflected.body.body.basicBlocks[6]'(by with_unfolding_all decide +kernel)
    have blockAt : caller.body.basicBlocks[6]? = some block := by rw [body];simp [block]
    have noStatement : block.statements[8]? = none := by with_unfolding_all rfl
    apply GenericCallStages.source_step cfg limits () (Storage.withCurrent #[] caller beforeMachine) (Storage.withCurrent #[] caller machine) _ caller ⟨6,8⟩ block
      HelperCompilerFacts.asMutPtrCall.function #[AsMutEvaluateCall.argument] ⟨15,#[]⟩ (some 7) .Continue AsMutCallTerminator.sourceKind AsMutCallTerminator.fnSpan
      (by simp [Storage.withCurrent,Stack.currentFrame?]) located blockAt noStatement AsMutCallTerminator.source_call accounting' call.2
    simp [Storage.withCurrent]
  have fields : resultMachine.user.payload.ghost = machine.user.payload.ghost ∧
      resultMachine.user.payload.validation = machine.user.payload.validation ∧ resultMachine.user.addresses = machine.user.addresses ∧
      resultMachine.user.payload.payload.user = machine.user.payload.payload.user := by
    dsimp only [resultMachine,TypedBorrowSteps.registeredMachine,ReferenceBorrowDriver.allocatedMachine,post,
      AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,before,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact ⟨rfl,rfl,rfl,rfl⟩
  let resultEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := entry.allocation.setExtra finalTree}
  have resultPresent : resultMachine.memory.live.find? (fun row => row.1 == id) = some (id,resultEntry) :=
    MemoryCopyBridge.live_lookup_replaced post.memory id resultEntry
  have carrier : AsMutPtrCarrier.Valid resultMachine (.inl pointer) len :=
    .positive id tracker.global.nextPointerTag base offset len resultEntry (by rw [fields.2.2.1];exact cachedAddress)
      resultPresent positive nonzero signedFits bounds
  have slots := AsMutInitializedShape.locals options before destination value adjusted id tracker.global.nextPointerTag
  have frameFacts := AsMutInitializedShape.fixed options before destination value adjusted id tracker.global.nextPointerTag
  have size : frame.locals.size = 5 := by rw [show frame.locals = _ from slots];rfl
  have frameRace : frame.extra.dataRace = none := by
    change machine.dataRace.map _ = none
    rw [race];rfl
  obtain ⟨done,trace,bodyDone,identityDone,calleeDone,extra,returnPlace,continuation,varargs,localsId,sourceDone,sizeDone,locationDone,pointerDone,dead2,dead3,dead4⟩ :=
    AsMutPtrBody.actual_ten_statements options limits remaining span debugOff validityFuel validationEq
      #[cf] frame resultMachine pointer len carrier size
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      frameFacts.1 frameFacts.2.1 frameFacts.2.2.1 frameFacts.2.2.2.1 frameRace
      (TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag)
      rfl defaultMode (fields.1.trans ghost) (fields.2.1.trans shallow) dynamicFuel fuelEq cmp
      (by change resultMachine.user.payload.payload.user.types.metadata = _;rw [fields.2.2.2];exact metadata)
      (by change resultMachine.user.payload.payload.user.types.entries.any _ = _;rw [fields.2.2.2];exact notConstructed)
  have direct := direct_of_slots done sizeDone _ adjusted
    (by rw [pointerDone];rfl) (by rw [sourceDone,slots];rfl) dead2 dead3 dead4
  refine ⟨done,.next entered trace,bodyDone.trans frameFacts.1,identityDone.trans frameFacts.2.1,
    calleeDone.trans frameFacts.2.2.1,sizeDone,locationDone,pointerDone,sourceDone,dead2,dead3,dead4,extra,?_,?_,?_,?_,?_,direct⟩
  · rw [extra];exact frameFacts.2.2.2.2.2.2.2
  · rw [extra];exact frameRace
  · exact returnPlace.trans frameFacts.2.2.2.2.1
  · exact continuation.trans frameFacts.2.2.2.2.2.1
  · exact varargs.trans frameFacts.2.2.2.2.2.2.1

def rawResult (span : PreparedContracts.FixedSpanQuery) : Scalar Provenance := Scalar.fromPointer
  (config options (remaining+1) span).access.runtime.base
  (Pointer.new (.concrete sourceId PureTree.helperTracker.global.nextPointerTag) (Size.ofBytes 4096))

/-- Same closed call through the actual as_mut_ptr Return. -/
theorem initializes_through_as_mut_with_frame (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator) (compare : PreparedContracts.SourceComparator) :
    let cfg := config options (remaining+1) span
    ∃ updated : Allocation Provenance BorrowTree, ∃ finished : RootState,
      initializationResult span = .ok () (S05ZeroCellActualCallInit.installed span updated) ∧
      SuccessfulTrace.Trace cfg limits (S05ZeroCellActualCallInit.installed span updated) finished ∧
      (S05ZeroCellActualCallInit.installed span updated).stack.frames.size = 1 ∧ finished.stack.frames.size = 1 ∧
      finished.stack.currentFrame?.map (·.location) = some (.mir ⟨7,0⟩) ∧
      (finished.stack.currentFrame?.bind fun frame => frame.locals[15]?) =
        some ⟨.live (.immediate (.scalar (rawResult span))),some CopyCompilerFacts.destPointerLayout⟩ ∧
      ∃ finalCaller : CompilerFrameContext.ActualFrame, ∃ finalValid : 15 < finalCaller.locals.size,
      ∃ helperFrame : CompilerFrameContext.ActualFrame,
      ∃ helperMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      ∃ finalMemory : MemoryState Provenance BorrowTree MiriMemoryKind,
      ∃ helperTracker : MachineHooks.BorrowState, ∃ helperLoan : FrameState, ∃ helperThread : ThreadRecord,
        finished = Storage.withCurrent #[]
          {AsMutPtrReturn.writeFrame finalCaller 15 (.scalar (rawResult span)) finalValid with location := .mir ⟨7,0⟩}
          (AsMutPtrReturn.poppedMachine #[] finalCaller helperFrame
            (ActualPopPlan.released (AsMutPtrReturn.accountedMachine options remaining span helperMachine)
              finalMemory helperTracker helperLoan) (helperThread.topUserRelevantFrame.getD 1)) ∧
        helperMachine.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,
          {S05ZeroCellActualCallLenReturn.source with allocation :=
            S05ZeroCellActualCallLenReturn.source.allocation.setExtra PureTree.helperChild.tree}) ∧
        helperMachine.borrowTracker = some helperTracker ∧
        helperTracker = TypedBorrowSteps.registeredTracker
          (ReferenceBorrowDriver.allocatedTracker PureTree.afterDefaultTracker PureTree.helperFresh)
          PureTree.afterDefaultTracker.global.nextPointerTag ∧
        helperLoan = ({} : FrameState).addProtector sourceId PureTree.afterDefaultTracker.global.nextPointerTag ∧
        finalMemory = StackPopRelease.commitTree helperMachine.memory sourceId
          {S05ZeroCellActualCallLenReturn.source with allocation :=
            S05ZeroCellActualCallLenReturn.source.allocation.setExtra PureTree.helperChild.tree} PureTree.released.tree ∧
        helperMachine.user.addresses.baseAddr.find? (fun row => row.allocId == sourceId) = some ⟨sourceId,4096⟩ ∧
        helperMachine.user.payload.payload.user.types = PreparedReflection.actual.types ∧
        helperMachine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == sourceId) =
          some (sourceId,⟨none,#[]⟩) ∧
        helperMachine.user.payload.payload.user.backend = .none ∧
        helperMachine.user.payload.ghost = false ∧ helperMachine.user.payload.validation = .Shallow ∧
        helperMachine.dataRace = none ∧
        (cfg.terminators.getControl helperMachine.user).checkedArithmetic = false ∧
        (cfg.terminators.getControl helperMachine.user).gcInterval = 0 ∧
        helperMachine.threads.fixedScheduling = true ∧
        helperMachine.threads.activeThread? = some helperThread ∧
        (∀ index,helperThread.topUserRelevantFrame = some index → index < 2) ∧
        ∃ original prepared : CompilerFrameContext.ActualFrame, ∃ valid16 : 16 < prepared.locals.size,
        ∃ valid15 : 15 < (CopyHelperSteps.advance (ActualLocalCopy.written prepared 16
          (RootReferenceInfo.layout false) valid16
          (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete sourceId PureTree.returnedTracker.global.nextPointerTag) (Size.ofBytes 4096))
            2 (RootReferenceInfo.layout false)).imm) ⟨6,7⟩).locals.size,
          GenericFunctionEntryPrefix.Shape
            ((S05ZeroCellActualCallInit.installed span updated).stack.frames[0]'(by change 0 < 1; decide)) original 1 ∧
          finalCaller = AsMutUncachedCall.cachedCaller (CopyHelperSteps.advance
            (ActualLocalCopy.written prepared 16 (RootReferenceInfo.layout false) valid16
              (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
                (Pointer.new (.concrete sourceId PureTree.returnedTracker.global.nextPointerTag) (Size.ofBytes 4096))
                2 (RootReferenceInfo.layout false)).imm) ⟨6,7⟩) valid15 ∧
          prepared.body = RootBody.reflected.body.body ∧ prepared.bodyIdentity = RootBody.reflected.body.identity ∧
          prepared.functionInstance = RootBody.reflected.functionInstance ∧ prepared.extra = original.extra ∧
          prepared.trackCallerArg = original.trackCallerArg ∧ prepared.locals.size = 25 ∧
          prepared.locals[2]? = original.locals[2]? ∧
          (∀ index,17 ≤ index → prepared.locals[index]? = original.locals[index]?) ∧
          CopyHelperCleanup.AllImmediate prepared ∧
          (∀ other otherEntry, other ≠ sourceId →
            (S05ZeroCellActualCallSharedStmt.postMachine span updated).memory.live.find? (fun row => row.1 == other) = some (other,otherEntry) →
            helperMachine.memory.live.find? (fun row => row.1 == other) = some (other,otherEntry)) ∧
          helperMachine.user.addresses = (S05ZeroCellActualCallSharedStmt.postMachine span updated).user.addresses ∧
          helperMachine.user.payload.payload.user.runtime.extras = (S05ZeroCellActualCallSharedStmt.postMachine span updated).user.payload.payload.user.runtime.extras ∧
          prepared.returnPlace = original.returnPlace ∧ prepared.returnContinuation = original.returnContinuation ∧
          prepared.vaList = original.vaList ∧ prepared.localsIdentity = original.localsIdentity ∧
          prepared.locals[0]? = original.locals[0]? := by
  obtain ⟨updated,lenFinal,init,lenTrace,depth,lenDepth,lenLocation,lenValue,
    caller,callerValid,helper,doneMachine,releasedMemory,held,loan,thread,finalEq,
    memoryEq,tracked,heldEq,loanEq,releasedEq,addresses,types,extras,ghost,shallow,race,active,returnFacts,rootCache,
    original,valid12,shape,validCall,callerEq⟩ := S05ZeroCellActualCallLenReturn.initializes_through_len span cmp compare
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span rfl rfl
  let frame : CompilerFrameContext.ActualFrame :=
    {PtrMetadataExecution.writeFrame caller 11 (.scalar (.fromScalarInt (.ofUInt64 2))) callerValid with location := .mir ⟨3,0⟩}
  let machine := PtrMetadataReturn.poppedMachine #[] caller helper
    (ActualPopPlan.released (PtrMetadataReturn.accountedMachine options remaining span doneMachine) releasedMemory held loan)
    (thread.topUserRelevantFrame.getD 1)
  change lenFinal = Storage.withCurrent #[] frame machine at finalEq
  rw [finalEq] at lenTrace
  let source : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {S05ZeroCellActualCallLenReturn.source with allocation := S05ZeroCellActualCallLenReturn.source.allocation.setExtra PureTree.tree}
  have sourceMemory : machine.memory = RetagEntry.updatedMemory
      (S05ZeroCellActualCallSharedStmt.postMachine span updated).memory sourceId S05ZeroCellActualCallLenReturn.source PureTree.tree := by
    unfold machine PtrMetadataReturn.poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> change releasedMemory = _
    all_goals
      rw [releasedEq,memoryEq]
      exact RetagEntry.updated_memory_twice _ _ _ _ _
  have sourcePresent : machine.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,source) := by
    rw [sourceMemory]
    exact StackPopRelease.lookup_commit_same _ sourceId S05ZeroCellActualCallLenReturn.source PureTree.tree
  have trackerEnabled : machine.borrowTracker = some PureTree.returnedTracker := by
    unfold machine PtrMetadataReturn.poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> simp only [ActualPopPlan.released,heldEq,loanEq,PureTree.returnedTracker,PureTree.lenHeld,PureTree.loan] <;> rfl
  have user : machine.user = (PtrMetadataReturn.accountedMachine options remaining span doneMachine).user :=
    PtrMetadataReturn.popped_user _ _ _ _ _
  have doneGhost : machine.user.payload.ghost = false := by
    rw [user,PtrMetadataReturn.accounted_ghost]
    exact ghost
  have doneShallow : machine.user.payload.validation = .Shallow := by
    rw [user,PtrMetadataReturn.accounted_validation]
    exact shallow
  have doneRace : machine.dataRace = none := by
    unfold machine PtrMetadataReturn.poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> exact race
  have unchecked : ((config options (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false := by
    rw [user]
    exact (RootZeroCompleteState.tick_flags options remaining span doneMachine).1.trans returnFacts.unchecked
  have noGc : ((config options (remaining+1) span).terminators.getControl machine.user).gcInterval = 0 := by
    rw [user]
    exact (RootZeroCompleteState.tick_flags options remaining span doneMachine).2.trans returnFacts.noGc
  have fixed : machine.threads.fixedScheduling = true := by
    unfold machine PtrMetadataReturn.poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> exact returnFacts.fixed
  obtain ⟨boundedThread,boundedActive,cacheBound⟩ := rootCache.bound rfl
  have sameThread : thread = boundedThread := Option.some.inj (active.symm.trans boundedActive)
  have bound : ∀ index,thread.topUserRelevantFrame = some index → index < 2 := by rw [sameThread];exact cacheBound
  let releasedMachine := ActualPopPlan.released (PtrMetadataReturn.accountedMachine options remaining span doneMachine) releasedMemory held loan
  have releasedActive : releasedMachine.threads.activeThread? = some thread := active
  obtain ⟨rootThread,rootActive,rootCacheZero⟩ := GeneralBorrowForestAcceptedAfterLenCache.pop releasedMachine caller helper thread releasedActive bound
  change machine.threads.activeThread? = some rootThread at rootActive
  let raw := RawRootInvocation.root before place profile.2.2.2.1
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete sourceId S05ZeroCellActualCallSharedStmt.PureTree.initialGlobal.nextPointerTag)
      (Size.ofBytes 4096)) 2 ActualReferenceMetadata.reference).imm
  let start := PositiveRootInstalledFrame.installed raw adjusted 1 {} sourceId
    S05ZeroCellActualCallSharedStmt.PureTree.initialGlobal.nextPointerTag destinationId
    S05ZeroCellActualCallSharedStmt.PureTree.tracker9.global.nextPointerTag
  change GenericFunctionEntryPrefix.Shape start original 1 at shape
  obtain ⟨body0,identity0,callee0,cont0,place0,va0,clocks0,borrow0,location0⟩ :=
    PositiveRootInstalledFrame.metadata raw adjusted 1 {} sourceId
      S05ZeroCellActualCallSharedStmt.PureTree.initialGlobal.nextPointerTag destinationId
      S05ZeroCellActualCallSharedStmt.PureTree.tracker9.global.nextPointerTag
  have body : frame.body = RootBody.reflected.body.body := by
    simpa only [frame,PtrMetadataExecution.writeFrame,callerEq,cachedCaller,AsMutUncachedCall.cachedCaller,
      LenUncachedFrontend.cachedCaller,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]
      using shape.body.trans (body0.trans raw.body)
  have identity : frame.bodyIdentity = RootBody.reflected.body.identity := by
    simpa only [frame,PtrMetadataExecution.writeFrame,callerEq,LenUncachedFrontend.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using shape.identity.trans (identity0.trans raw.identity)
  have callee : frame.functionInstance = RootBody.reflected.functionInstance := by
    simpa only [frame,PtrMetadataExecution.writeFrame,callerEq,LenUncachedFrontend.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using shape.callee.trans (callee0.trans raw.callee)
  have size : frame.locals.size = 25 := by simp [frame,PtrMetadataExecution.writeFrame,callerEq,LenUncachedFrontend.cachedCaller,
    CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,shape.size]
  have originalSize : original.locals.size = 25 := shape.size
  have kept (i : Fin 25) (n11 : 11 ≠ i.val) (n12 : 12 ≠ i.val) :
      frame.locals[i.val]'(by rw [size]; exact i.isLt) = original.locals[i.val]'(by rw [originalSize]; exact i.isLt) := by
    simp [frame,PtrMetadataExecution.writeFrame,callerEq,LenUncachedFrontend.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,n11,n12]
  have initialSlot (i : Fin 25) (same : original.locals[i.val]? = start.locals[i.val]?) :
      original.locals[i.val]'(by rw [originalSize];exact i.isLt) =
      if 14 = i.val ∨ 13 = i.val ∨ 6 = i.val ∨ 0 = i.val then ⟨.live (.immediate .uninit),none⟩
      else if 2 = i.val then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 1)))),some RootCompilerFacts.usizeLayout⟩
      else if 1 = i.val then ⟨.live (.immediate adjusted),some ActualReferenceMetadata.reference⟩ else ⟨.dead,none⟩ := by
    have known := PositiveRootInstalledFrame.slot_option raw (RawRootInvocation.locals before place profile.2.2.2.1)
      adjusted 1 {} sourceId S05ZeroCellActualCallSharedStmt.PureTree.initialGlobal.nextPointerTag
      destinationId S05ZeroCellActualCallSharedStmt.PureTree.tracker9.global.nextPointerTag i
    exact Option.some.inj ((Array.getElem?_eq_getElem (by rw [originalSize];exact i.isLt)).symm.trans (same.trans known))
  have o0 := initialSlot ⟨0,by decide⟩ shape.slot0
  have o13 := initialSlot ⟨13,by decide⟩ (shape.keep 13 (by decide))
  have o15 := initialSlot ⟨15,by decide⟩ (shape.keep 15 (by decide))
  have o16 := initialSlot ⟨16,by decide⟩ (shape.keep 16 (by decide))
  have originalKnown (i : Nat) (valid : i < original.locals.size)
      (value : LocalState Provenance LocalLayout) (known : original.locals[i]? = some value) : original.locals[i] = value :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans known)
  have o7 := originalKnown 7 (by rw [originalSize];decide) _ shape.slot7
  have o8 := originalKnown 8 (by rw [originalSize];decide) _ shape.slot8
  have o9 := originalKnown 9 (by rw [originalSize];decide) _ shape.slot9
  have o10 := originalKnown 10 (by rw [originalSize];decide) _ shape.slot10
  have f0 : frame.locals[0] = ⟨.live (.immediate .uninit),none⟩ := by rw [kept ⟨0,by decide⟩ (by decide) (by decide)]; simpa using o0
  have f7 : frame.locals[7] = ⟨.live (.immediate .uninit),none⟩ := by rw [kept ⟨7,by decide⟩ (by decide) (by decide)]; exact o7
  have f8 : frame.locals[8] = ⟨.live (.immediate .uninit),none⟩ := by rw [kept ⟨8,by decide⟩ (by decide) (by decide)]; exact o8
  have f9 : frame.locals[9] = ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 1)))),some RootCompilerFacts.usizeLayout⟩ := by
    rw [kept ⟨9,by decide⟩ (by decide) (by decide)]; exact o9
  have f10 : frame.locals[10] = ⟨.live (.immediate .uninit),none⟩ := by rw [kept ⟨10,by decide⟩ (by decide) (by decide)]; exact o10
  have f13 : frame.locals[13] = ⟨.live (.immediate .uninit),none⟩ := by rw [kept ⟨13,by decide⟩ (by decide) (by decide)]; simpa using o13
  have f15 : frame.locals[15] = ⟨.dead,none⟩ := by rw [kept ⟨15,by decide⟩ (by decide) (by decide)]; simpa using o15
  have f16 : frame.locals[16] = ⟨.dead,none⟩ := by rw [kept ⟨16,by decide⟩ (by decide) (by decide)]; simpa using o16
  have f11 : frame.locals[11] = ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 2)))),some RootCompilerFacts.usizeLayout⟩ := by
    simp [frame,PtrMetadataExecution.writeFrame,callerEq,LenUncachedFrontend.cachedCaller,LocalPlaces.cachePlaceLayout]
  have f12 : frame.locals[12].value = .live (.immediate (S05ZeroCellActualCallSharedStmt.value span).imm) := by
    simp [frame,PtrMetadataExecution.writeFrame,callerEq,LenUncachedFrontend.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set]
  have clocks : frame.extra.dataRace = none := by
    simpa only [frame,PtrMetadataExecution.writeFrame,callerEq,LenUncachedFrontend.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using
      (congrArg (·.dataRace) shape.extra).trans (clocks0.trans raw.noClocks)
  have callerAll : CopyHelperCleanup.AllImmediate caller := by
    rw [callerEq]
    exact CopyHelperCleanup.all_immediate_cache _ 11 _ validCall
      (CopyHelperCleanup.all_immediate_written _ 12 _ _ valid12 shape.immediate)
  have all : CopyHelperCleanup.AllImmediate frame := by
    apply CopyHelperCleanup.all_immediate_set caller 11 _ callerValid callerAll
    intro memory
    simp
  have original1 := initialSlot ⟨1,by decide⟩ shape.slot1
  have f1 : frame.locals[1]? = some ⟨.live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new (.concrete sourceId PureTree.parent) (Size.ofBytes 4096))
      2 ActualReferenceMetadata.reference).imm),some ActualReferenceMetadata.reference⟩ := by
    rw [Array.getElem?_eq_getElem (by rw [size];decide),kept ⟨1,by decide⟩ (by decide) (by decide)]
    simpa only [Fin.val_mk,show ¬(14=1 ∨ 13=1 ∨ 6=1 ∨ 0=1) by decide,ite_false,
      show ¬(2=1) by decide,show (1=1) by rfl,ite_true,adjusted,PureTree.parent] using congrArg some original1
  have cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == sourceId) = some ⟨sourceId,4096⟩ := by
    rw [user]
    unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    change doneMachine.user.addresses.baseAddr.find? _ = _
    rw [addresses]
    unfold S05ZeroCellActualCallSharedStmt.postMachine S05ZeroCellActualCallSharedStmt.current RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact source_cached
  have currentTypes : machine.user.payload.payload.user.types = PreparedReflection.actual.types := by
    rw [user]
    unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    change doneMachine.user.payload.payload.user.types = _
    rw [types]
    unfold S05ZeroCellActualCallSharedStmt.postMachine S05ZeroCellActualCallSharedStmt.current RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    rfl
  have metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime := by rw [currentTypes];rfl
  have notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false := by rw [currentTypes];decide +kernel
  obtain ⟨prepared,valid16,defaultTrace,pbody,pidentity,pcallee,pextra,preturn,pcontinuation,pva,plocalsId,ptrack,psize,plocation,p1,p15,p2,pkeep,p0,pall⟩ :=
    default_step options limits remaining span compare ctx cmp remaining rfl rfl remaining rfl
    frame machine size (S05ZeroCellActualCallSharedStmt.value span).imm f12
    (congrArg LocalState.value f13) (congrArg LocalState.layout f13)
    (congrArg LocalState.value f0) (congrArg LocalState.layout f0)
    (congrArg LocalState.value f7) (congrArg LocalState.layout f7)
    (congrArg LocalState.value f15) (congrArg LocalState.layout f15)
    (congrArg LocalState.value f16) (congrArg LocalState.layout f16)
    (congrArg LocalState.value f8) (congrArg LocalState.layout f8)
    (congrArg LocalState.value f9) (congrArg LocalState.layout f9)
    (congrArg LocalState.value f10) (congrArg LocalState.layout f10)
    (congrArg LocalState.value f11) (congrArg LocalState.layout f11)
    body identity callee rfl all clocks PureTree.returnedTracker trackerEnabled rfl doneGhost doneShallow unchecked noGc fixed
    sourceId source 4096 (by decide) (by decide) rfl rfl rfl cachedAddress sourcePresent doneRace metadata notConstructed f1
  let twice := tick options remaining span (tick options remaining span machine)
  let mutableValue := RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete sourceId PureTree.returnedTracker.global.nextPointerTag) (Size.ofBytes 4096)) 2 (RootReferenceInfo.layout false)
  let callFrame := CopyHelperSteps.advance (ActualLocalCopy.written prepared 16 (RootReferenceInfo.layout false) valid16 mutableValue.imm) ⟨6,7⟩
  let beforeCall := {ReferenceBorrowDriver.allocatedMachine twice PureTree.returnedTracker PureTree.fresh with
    memory := RetagEntry.updatedMemory twice.memory sourceId source PureTree.defaultChild.tree}
  change SuccessfulTrace.Trace (config options (remaining+1) span) limits (Storage.withCurrent #[] frame machine)
    (Storage.withCurrent #[] callFrame beforeCall) at defaultTrace
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {source with allocation := source.allocation.setExtra PureTree.defaultChild.tree}
  let callMachine := AsMutPtrReturn.accountedMachine options remaining span beforeCall
  have callTracked : callMachine.borrowTracker = some PureTree.afterDefaultTracker := rfl
  have valid15 : 15 < callFrame.locals.size := by simp [callFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,psize]
  have validSource : 16 < callFrame.locals.size := by simp [callFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,psize]
  have cell15 : callFrame.locals[15] = ⟨.live (.immediate .uninit),none⟩ := by
    have old := Option.some.inj ((Array.getElem?_eq_getElem (show 15 < prepared.locals.size by rw [psize];decide)).symm.trans p15)
    simpa [callFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using old
  have value16 : callFrame.locals[16].value = .live (.immediate mutableValue.imm) := by
    simp [callFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]
  have cached16 : callFrame.locals[16].layout = some ActualReferenceMetadata.reference := by
    simp [callFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootReferenceInfo.layout]
  have callClocks : callFrame.extra.dataRace = none := by
    simpa only [callFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using
      (congrArg (·.dataRace) pextra).trans clocks
  have callEnv : callMachine.user.addresses = machine.user.addresses ∧
      callMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      callMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      callMachine.user.payload.ghost = machine.user.payload.ghost ∧
      callMachine.user.payload.validation = machine.user.payload.validation := by
    unfold callMachine AsMutPtrReturn.accountedMachine beforeCall twice RootZeroCompleteState.tick SourceControl.accounted
    simp only [(actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  have callGhost : callMachine.user.payload.ghost = false := callEnv.2.2.2.1.trans doneGhost
  have callShallow : callMachine.user.payload.validation = .Shallow := callEnv.2.2.2.2.trans doneShallow
  have callRace : callMachine.dataRace = none := doneRace
  have callPresent : callMachine.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,entry) :=
    StackPopRelease.lookup_commit_same twice.memory sourceId source PureTree.defaultChild.tree
  have callAddress : callMachine.user.addresses.baseAddr.find? (fun row => row.allocId == sourceId) = some ⟨sourceId,4096⟩ := by rw [callEnv.1];exact cachedAddress
  have callMetadata : callMachine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime := by rw [callEnv.2.1];exact metadata
  have callNotConstructed : callMachine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false := by rw [callEnv.2.1];exact notConstructed
  have callActive : callMachine.threads.activeThread? = some rootThread := by
    change twice.threads.activeThread? = some rootThread
    unfold twice
    rw [(RootZeroInvocationState.tick_fields options remaining span _).2.2.2.1,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.1]
    exact rootActive
  let cachedRoot := AsMutUncachedCall.cachedCaller callFrame valid15
  let destination := (LocalPlaces.localRuntimePlace 0 cachedRoot 15 CopyCompilerFacts.destPointerLayout).stackView
  let callState := Storage.withCurrent #[] cachedRoot callMachine
  have top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates callState destination).stack
      rootThread.topUserRelevantFrame = some 0 := by simp [FrameRelevance.top,rootCacheZero]
  have current : (AsMutPush.pushed options.userRelevantCrates callState destination).stack.frames[0]? = some cachedRoot := by
    simp [AsMutPush.pushed,callState,Storage.withCurrent]
  have backend : machine.user.payload.payload.user.backend = .none := by
    rw [user]
    unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact returnFacts.backend
  have callBackend : callMachine.user.payload.payload.user.backend = .none := callEnv.2.2.1.trans backend
  have callUnchecked : ((config options (remaining+1) span).terminators.getControl beforeCall.user).checkedArithmetic = false := by
    change ((config options (remaining+1) span).terminators.getControl twice.user).checkedArithmetic = false
    exact (tick_flags options remaining span _).1.trans ((tick_flags options remaining span machine).1.trans unchecked)
  have callNoGc : ((config options (remaining+1) span).terminators.getControl beforeCall.user).gcInterval = 0 := by
    change ((config options (remaining+1) span).terminators.getControl twice.user).gcInterval = 0
    exact (tick_flags options remaining span _).2.trans ((tick_flags options remaining span machine).2.trans noGc)
  have callFixed : beforeCall.threads.fixedScheduling = true := fixed
  obtain ⟨done,bodyTrace,doneBody,doneIdentity,doneCallee,doneSize,doneLocation,doneValue,doneArgument,
    done2,done3,done4,doneExtra,doneFrameTracked,doneClocks,doneDestination,doneContinuation,doneVarargs,doneDirect⟩ :=
    before_return options limits remaining 999999 rfl span ctx rfl cmp remaining remaining rfl rfl sourceId entry 4096 0 2
      PureTree.tracker.global.nextPointerTag rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
      callFrame callMachine PureTree.afterDefaultTracker callTracked rfl rfl rfl PureTree.helperFresh
      (pbody.trans body) (pidentity.trans identity) (pcallee.trans callee) rfl compare validSource value16 cached16
      valid15 .uninit (congrArg LocalState.value cell15) (congrArg LocalState.layout cell15) callClocks
      callGhost callShallow callAddress callPresent callRace callBackend callMetadata callNotConstructed
      rootThread 0 cachedRoot callActive top current beforeCall rfl callUnchecked callNoGc callFixed
  let pushed := (AsMutPush.completed options.userRelevantCrates callState destination cachedRoot).machine
  let finalTree := helperTree entry.allocation.extra PureTree.afterDefaultTracker PureTree.tracker.global.nextPointerTag 0 2
  have treeEq : finalTree = PureTree.helperChild.tree := rfl
  let helperMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine pushed PureTree.afterDefaultTracker PureTree.helperFresh)
      (ReferenceBorrowDriver.allocatedTracker PureTree.afterDefaultTracker PureTree.helperFresh) PureTree.afterDefaultTracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory pushed.memory sourceId entry finalTree}
  change SuccessfulTrace.Trace (config options (remaining+1) span) limits (Storage.withCurrent #[] callFrame beforeCall)
    (Storage.withCurrent #[cachedRoot] done helperMachine) at bodyTrace
  let helperHeld := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker PureTree.afterDefaultTracker PureTree.helperFresh)
    PureTree.afterDefaultTracker.global.nextPointerTag
  let helperLoan := ({} : FrameState).addProtector sourceId PureTree.afterDefaultTracker.global.nextPointerTag
  let helperEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := entry.allocation.setExtra finalTree}
  have helperPresent : helperMachine.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,helperEntry) :=
    StackPopRelease.lookup_commit_same pushed.memory sourceId entry finalTree
  have helperTracked : helperMachine.borrowTracker = some helperHeld := rfl
  have released : finalTree.releaseProtector PureTree.afterDefaultTracker.global.nextPointerTag helperHeld.global.protectedTags =
      ⟨PureTree.released.tree,.Released⟩ := by
    simpa only [treeEq,helperHeld,PureTree.helperTracker,PureTree.heldGlobal,
      TypedBorrowSteps.registeredTracker,ReferenceBorrowDriver.allocatedTracker,TypedBorrowSteps.registeredGlobal]
      using PureTree.actual_release
  let finalMemory := StackPopRelease.commitTree helperMachine.memory sourceId helperEntry PureTree.released.tree
  have plan : StackPopRelease.Plan helperHeld.global.protectedTags helperLoan.protectedTags.toList helperMachine.memory finalMemory :=
    StackPopRelease.Plan.live sourceId PureTree.afterDefaultTracker.global.nextPointerTag helperEntry PureTree.released.tree []
      helperMachine.memory _ helperPresent released (.nil _)
  let supply := AsMutPush.fresh callMachine
  let pushedFrame := AsMutFrame.rawFrame options.userRelevantCrates supply.1 destination supply.2
  let helperThread := PushThread.after rootThread 1 pushedFrame.extra.userRelevance cachedRoot.extra.userRelevance
  have freshActive : supply.1.threads.activeThread? = some rootThread := callActive
  have helperActive : helperMachine.threads.activeThread? = some helperThread := by
    have known := PushThread.active_after supply.1 rootThread 1 pushedFrame.extra.userRelevance cachedRoot.extra.userRelevance freshActive
    simpa only [helperMachine,TypedBorrowSteps.registeredMachine,ReferenceBorrowDriver.allocatedMachine,pushed,
      AsMutPush.completed,callState,Storage.withCurrent,Array.size_push,Array.size_empty,Nat.zero_add,supply,pushedFrame] using known
  have helperThreadBound : ∀ index,helperThread.topUserRelevantFrame = some index → index < 2 := by
    intro index h
    dsimp only [helperThread,PushThread.after] at h
    split at h
    · have one := Option.some.inj h; omega
    · rw [rootCacheZero] at h
      have zero := Option.some.inj h; omega
  have helperFields : helperMachine.user.payload.ghost = callMachine.user.payload.ghost ∧
      helperMachine.user.payload.validation = callMachine.user.payload.validation ∧
      helperMachine.user.addresses = callMachine.user.addresses ∧
      helperMachine.user.payload.payload.user = callMachine.user.payload.payload.user := by
    dsimp only [helperMachine,TypedBorrowSteps.registeredMachine,ReferenceBorrowDriver.allocatedMachine,pushed,
      AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,callState,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact ⟨rfl,rfl,rfl,rfl⟩
  have helperUser : helperMachine.user = supply.1.user := by
    dsimp only [helperMachine,TypedBorrowSteps.registeredMachine,ReferenceBorrowDriver.allocatedMachine,pushed,
      AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,callState,Storage.withCurrent,GenericPushRelevance.afterPush,supply]
    split <;> rfl
  have helperControl : (config options (remaining+1) span).terminators.getControl helperMachine.user =
      (config options (remaining+1) span).terminators.getControl callMachine.user := by
    rw [helperUser]
    simpa only [RawRootInvocation.machine,CallEntryFacts.cacheTop,supply,AsMutPush.fresh] using
      RootZeroInvocationState.raw_control options remaining span callMachine
  have helperFlags : ((config options (remaining+1) span).terminators.getControl helperMachine.user).checkedArithmetic = false ∧
      ((config options (remaining+1) span).terminators.getControl helperMachine.user).gcInterval = 0 := by
    have flags := tick_flags options remaining span beforeCall
    change ((config options (remaining+1) span).terminators.getControl callMachine.user).checkedArithmetic =
      ((config options (remaining+1) span).terminators.getControl beforeCall.user).checkedArithmetic ∧
      ((config options (remaining+1) span).terminators.getControl callMachine.user).gcInterval =
      ((config options (remaining+1) span).terminators.getControl beforeCall.user).gcInterval at flags
    rw [helperControl]
    exact ⟨flags.1.trans callUnchecked,flags.2.trans callNoGc⟩
  have helperFixed : helperMachine.threads.fixedScheduling = true := by
    dsimp only [helperMachine,TypedBorrowSteps.registeredMachine,ReferenceBorrowDriver.allocatedMachine,pushed,AsMutPush.completed,
      AsMutPush.fresh,CallEntryFacts.freshRoot,callState,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact callFixed
  have helperGhost : helperMachine.user.payload.ghost = false := helperFields.1.trans callGhost
  have helperShallow : helperMachine.user.payload.validation = .Shallow := helperFields.2.1.trans callShallow
  have cachedValid : 15 < cachedRoot.locals.size := by simpa [cachedRoot,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using valid15
  have cachedLive : cachedRoot.locals[15].value = .live (.immediate .uninit) := by
    simpa [cachedRoot,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using congrArg LocalState.value cell15
  have cachedLayout : cachedRoot.locals[15].layout = some CopyCompilerFacts.destPointerLayout := by
    simp [cachedRoot,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout]
  have valid0 : 0 < done.locals.size := by rw [doneSize];decide
  have returnedCell : done.locals[0]'valid0 = ⟨.live (.immediate (.scalar (rawResult span))),some CopyCompilerFacts.destPointerLayout⟩ := by
    have known := Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans doneValue)
    simpa only [rawResult,UInt64.add_zero,PureTree.helperTracker,ActualReferenceContext.config] using known
  have cachedClocks : cachedRoot.extra.dataRace = none := callClocks
  have returned := AsMutPtrReturn.return_step options limits remaining span rfl remaining rfl #[] cachedRoot done helperMachine
    (rawResult span) 15 doneBody doneLocation valid0 (congrArg LocalState.value returnedCell) (congrArg LocalState.layout returnedCell)
    doneClocks cachedValid cachedLive cachedLayout cachedClocks (by rw [doneDestination]; exact RuntimePlace.stackView_toRuntimePlace _)
    7 .Continue doneContinuation doneDirect doneVarargs helperHeld helperLoan helperTracked doneFrameTracked finalMemory plan
    helperThread helperActive helperFlags.1 helperFlags.2 helperFixed helperGhost helperShallow
  let final : RootState := Storage.withCurrent #[]
    {AsMutPtrReturn.writeFrame cachedRoot 15 (.scalar (rawResult span)) cachedValid with location := .mir ⟨7,0⟩}
    (AsMutPtrReturn.poppedMachine #[] cachedRoot done
      (ActualPopPlan.released (AsMutPtrReturn.accountedMachine options remaining span helperMachine) finalMemory helperHeld helperLoan)
      (helperThread.topUserRelevantFrame.getD 1))
  have returned' : ExecutionMachine.step (config options (remaining+1) span) limits ()
      (Storage.withCurrent #[cachedRoot] done helperMachine) = (final,.ok true) := by
    simpa [final,ActualReferenceContext.config] using returned
  refine ⟨updated,final,init,?_,depth,rfl,?_,?_,cachedRoot,cachedValid,done,helperMachine,finalMemory,helperHeld,helperLoan,helperThread,rfl,?_,helperTracked,rfl,rfl,?_,?_,?_,?_,?_,helperGhost,helperShallow,?_,helperFlags.1,helperFlags.2,helperFixed,helperActive,helperThreadBound,original,prepared,valid16,valid15,shape,rfl,pbody.trans body,pidentity.trans identity,pcallee.trans callee,?_,?_,psize,?_,?_,pall,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact SuccessfulTrace.append lenTrace (SuccessfulTrace.append defaultTrace (SuccessfulTrace.append bodyTrace (.next returned' (.refl _))))
  · simp only [final,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,Option.map_some]
  · simp [final,Storage.withCurrent,Stack.currentFrame?,AsMutPtrReturn.writeFrame,cachedLayout]
  · simpa only [helperEntry,entry,source,treeEq,Allocation.setExtra,Allocation.mapExtra] using helperPresent
  · rfl
  · rw [helperFields.2.2.1];exact callAddress
  · rw [helperFields.2.2.2,callEnv.2.1];exact currentTypes
  · rw [helperFields.2.2.2]
    unfold callMachine AsMutPtrReturn.accountedMachine beforeCall twice RootZeroCompleteState.tick SourceControl.accounted
    simp only [(actual_fields options () (remaining+1) span).terminators]
    rw [user]
    unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    change doneMachine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == sourceId) =
      some (sourceId,⟨none,#[]⟩)
    rw [extras]
    unfold S05ZeroCellActualCallSharedStmt.postMachine S05ZeroCellActualCallSharedStmt.current RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact source_extras
  · rw [helperFields.2.2.2,callEnv.2.2.1];exact backend
  · dsimp only [helperMachine,TypedBorrowSteps.registeredMachine,ReferenceBorrowDriver.allocatedMachine,pushed,
      AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,callState,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact callRace
  · exact pextra.trans (by
      simp only [frame,PtrMetadataExecution.writeFrame,callerEq,LenUncachedFrontend.cachedCaller,
        CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout])
  · exact ptrack.trans (by
      simp only [frame,PtrMetadataExecution.writeFrame,callerEq,LenUncachedFrontend.cachedCaller,
        CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout])
  · exact p2.trans (by
      simp only [frame,PtrMetadataExecution.writeFrame,callerEq,LenUncachedFrontend.cachedCaller,
        CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,show ¬(11=2) by decide,show ¬(12=2) by decide,ite_false])
  · intro index lower
    apply (pkeep index lower).trans
    have ne11 : 11 ≠ index := by omega
    have ne12 : 12 ≠ index := by omega
    simp only [frame,PtrMetadataExecution.writeFrame,callerEq,LenUncachedFrontend.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,
      ne11,ne12,ite_false]

  · intro other otherEntry different earlier
    have atMachine : machine.memory.live.find? (fun row => row.1 == other) = some (other,otherEntry) := by
      rw [sourceMemory]
      exact StackPopRelease.lookup_commit_other _ sourceId other _ otherEntry _ different earlier
    have atTwice : twice.memory.live.find? (fun row => row.1 == other) = some (other,otherEntry) := atMachine
    have atBeforeCall : beforeCall.memory.live.find? (fun row => row.1 == other) = some (other,otherEntry) :=
      StackPopRelease.lookup_commit_other twice.memory sourceId other source otherEntry PureTree.defaultChild.tree different atTwice
    have atPushed : pushed.memory.live.find? (fun row => row.1 == other) = some (other,otherEntry) := by
      dsimp only [pushed,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,CallEntryFacts.cacheTop,callState,Storage.withCurrent,GenericPushRelevance.afterPush]
      split <;> exact atBeforeCall
    exact StackPopRelease.lookup_commit_other pushed.memory sourceId other entry otherEntry finalTree different atPushed
  · rw [helperFields.2.2.1,callEnv.1,user]
    unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact addresses
  · rw [helperFields.2.2.2]
    unfold callMachine AsMutPtrReturn.accountedMachine beforeCall twice RootZeroCompleteState.tick SourceControl.accounted
    simp only [(actual_fields options () (remaining+1) span).terminators]
    rw [user]
    unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact extras
  · simpa only [frame,PtrMetadataExecution.writeFrame,callerEq,LenUncachedFrontend.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using preturn
  · simpa only [frame,PtrMetadataExecution.writeFrame,callerEq,LenUncachedFrontend.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using pcontinuation
  · simpa only [frame,PtrMetadataExecution.writeFrame,callerEq,LenUncachedFrontend.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using pva
  · simpa only [frame,PtrMetadataExecution.writeFrame,callerEq,LenUncachedFrontend.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using plocalsId
  · simpa only [frame,PtrMetadataExecution.writeFrame,callerEq,LenUncachedFrontend.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,
      show ¬(11=0) by decide,show ¬(12=0) by decide,ite_false] using p0

/-- Retained prefix API; the stronger export also frames unrelated live allocations. -/
theorem initializes_through_as_mut (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator) (compare : PreparedContracts.SourceComparator) :
    let cfg := config options (remaining+1) span
    ∃ updated : Allocation Provenance BorrowTree, ∃ finished : RootState,
      initializationResult span = .ok () (S05ZeroCellActualCallInit.installed span updated) ∧
      SuccessfulTrace.Trace cfg limits (S05ZeroCellActualCallInit.installed span updated) finished ∧
      (S05ZeroCellActualCallInit.installed span updated).stack.frames.size = 1 ∧ finished.stack.frames.size = 1 ∧
      finished.stack.currentFrame?.map (·.location) = some (.mir ⟨7,0⟩) ∧
      (finished.stack.currentFrame?.bind fun frame => frame.locals[15]?) =
        some ⟨.live (.immediate (.scalar (rawResult span))),some CopyCompilerFacts.destPointerLayout⟩ ∧
      ∃ finalCaller : CompilerFrameContext.ActualFrame, ∃ finalValid : 15 < finalCaller.locals.size,
      ∃ helperFrame : CompilerFrameContext.ActualFrame,
      ∃ helperMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      ∃ finalMemory : MemoryState Provenance BorrowTree MiriMemoryKind,
      ∃ helperTracker : MachineHooks.BorrowState, ∃ helperLoan : FrameState, ∃ helperThread : ThreadRecord,
        finished = Storage.withCurrent #[]
          {AsMutPtrReturn.writeFrame finalCaller 15 (.scalar (rawResult span)) finalValid with location := .mir ⟨7,0⟩}
          (AsMutPtrReturn.poppedMachine #[] finalCaller helperFrame
            (ActualPopPlan.released (AsMutPtrReturn.accountedMachine options remaining span helperMachine)
              finalMemory helperTracker helperLoan) (helperThread.topUserRelevantFrame.getD 1)) ∧
        helperMachine.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,
          {S05ZeroCellActualCallLenReturn.source with allocation :=
            S05ZeroCellActualCallLenReturn.source.allocation.setExtra PureTree.helperChild.tree}) ∧
        helperMachine.borrowTracker = some helperTracker ∧
        helperTracker = TypedBorrowSteps.registeredTracker
          (ReferenceBorrowDriver.allocatedTracker PureTree.afterDefaultTracker PureTree.helperFresh)
          PureTree.afterDefaultTracker.global.nextPointerTag ∧
        helperLoan = ({} : FrameState).addProtector sourceId PureTree.afterDefaultTracker.global.nextPointerTag ∧
        finalMemory = StackPopRelease.commitTree helperMachine.memory sourceId
          {S05ZeroCellActualCallLenReturn.source with allocation :=
            S05ZeroCellActualCallLenReturn.source.allocation.setExtra PureTree.helperChild.tree} PureTree.released.tree ∧
        helperMachine.user.addresses.baseAddr.find? (fun row => row.allocId == sourceId) = some ⟨sourceId,4096⟩ ∧
        helperMachine.user.payload.payload.user.types = PreparedReflection.actual.types ∧
        helperMachine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == sourceId) =
          some (sourceId,⟨none,#[]⟩) ∧
        helperMachine.user.payload.payload.user.backend = .none ∧
        helperMachine.user.payload.ghost = false ∧ helperMachine.user.payload.validation = .Shallow ∧
        helperMachine.dataRace = none ∧
        (cfg.terminators.getControl helperMachine.user).checkedArithmetic = false ∧
        (cfg.terminators.getControl helperMachine.user).gcInterval = 0 ∧
        helperMachine.threads.fixedScheduling = true ∧
        helperMachine.threads.activeThread? = some helperThread ∧
        (∀ index,helperThread.topUserRelevantFrame = some index → index < 2) ∧
        ∃ original prepared : CompilerFrameContext.ActualFrame, ∃ valid16 : 16 < prepared.locals.size,
        ∃ valid15 : 15 < (CopyHelperSteps.advance (ActualLocalCopy.written prepared 16
          (RootReferenceInfo.layout false) valid16
          (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete sourceId PureTree.returnedTracker.global.nextPointerTag) (Size.ofBytes 4096))
            2 (RootReferenceInfo.layout false)).imm) ⟨6,7⟩).locals.size,
          GenericFunctionEntryPrefix.Shape
            ((S05ZeroCellActualCallInit.installed span updated).stack.frames[0]'(by change 0 < 1; decide)) original 1 ∧
          finalCaller = AsMutUncachedCall.cachedCaller (CopyHelperSteps.advance
            (ActualLocalCopy.written prepared 16 (RootReferenceInfo.layout false) valid16
              (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
                (Pointer.new (.concrete sourceId PureTree.returnedTracker.global.nextPointerTag) (Size.ofBytes 4096))
                2 (RootReferenceInfo.layout false)).imm) ⟨6,7⟩) valid15 ∧
          prepared.body = RootBody.reflected.body.body ∧ prepared.bodyIdentity = RootBody.reflected.body.identity ∧
          prepared.functionInstance = RootBody.reflected.functionInstance ∧ prepared.extra = original.extra ∧
          prepared.trackCallerArg = original.trackCallerArg ∧ prepared.locals.size = 25 ∧
          prepared.locals[2]? = original.locals[2]? ∧
          (∀ index,17 ≤ index → prepared.locals[index]? = original.locals[index]?) ∧
          CopyHelperCleanup.AllImmediate prepared := by
  obtain ⟨updated,finished,init,trace,depth,finishedDepth,location,value,
    caller,valid,helper,machine,memory,tracker,loan,thread,finishedEq,present,tracked,trackerEq,loanEq,memoryEq,
    cached,types,extras,backend,ghost,shallow,race,unchecked,noGc,fixed,active,bound,
    original,prepared,valid16,valid15,shape,callerEq,body,identity,callee,extra,track,size,slot2,keep,immediate,_,_,_,_,_,_,_,_⟩ :=
      initializes_through_as_mut_with_frame span cmp compare
  exact ⟨updated,finished,init,trace,depth,finishedDepth,location,value,
    caller,valid,helper,machine,memory,tracker,loan,thread,finishedEq,present,tracked,trackerEq,loanEq,memoryEq,
    cached,types,extras,backend,ghost,shallow,race,unchecked,noGc,fixed,active,bound,
    original,prepared,valid16,valid15,shape,callerEq,body,identity,callee,extra,track,size,slot2,keep,immediate⟩

end
end DuplicatePrefix.S05ZeroCellActualCallAsMutReturn
