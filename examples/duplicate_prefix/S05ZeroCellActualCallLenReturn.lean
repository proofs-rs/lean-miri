import duplicate_prefix.S05ZeroCellActualCallSharedStmt
import duplicate_prefix.ProtectedReferenceValidator
import duplicate_prefix.LenArgumentCopy
import duplicate_prefix.LenInstall
import duplicate_prefix.LenEntryShape
import duplicate_prefix.LenUncachedFrontend
import duplicate_prefix.MetadataCallStep
import duplicate_prefix.LenBodyFromEntry
import duplicate_prefix.LenReturnFromRelease
import duplicate_prefix.PushThread
import Init.Internal.Order.While

namespace DuplicatePrefix.S05ZeroCellActualCallLenReturn.PureTree
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

def tree : BorrowTree := S05ZeroCellActualCallSharedStmt.PureTree.child.tree
def parent : BorTag := S05ZeroCellActualCallSharedStmt.PureTree.global.nextPointerTag

theorem sharedFresh : S05ZeroCellActualCallSharedStmt.PureTree.global.nextPointerTag.value < 18446744073709551615 := by decide +kernel

def postSharedTracker : MachineHooks.BorrowState := ReferenceBorrowDriver.allocatedTracker
  ⟨S05ZeroCellActualCallSharedStmt.PureTree.global,.Default⟩ sharedFresh

def tracker : MachineHooks.BorrowState := {postSharedTracker with retagMode := .FnEntry}
theorem fresh : tracker.global.nextPointerTag.value < 18446744073709551615 := by decide +kernel

def heldGlobal : GlobalState := TypedBorrowSteps.registeredGlobal
  (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag

def read := tree.performBorrowAccessRange (.concrete parent) Size.ZERO
  (Size.ofBytes 2) .Read heldGlobal.protectedTags .VisitChildrenOfAccessed

def child := read.tree.newChild Size.ZERO (.concrete parent) tracker.global.nextPointerTag
  (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshAnchor.sharedState) .Frozen true

theorem read_complete : read.status = .Completed := by cbv

theorem child_complete : child.outcome = .ok () := by cbv

/-- The helper's tag is still protected during its actual end-access. -/
def releaseRead := child.tree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag) Size.ZERO
  (Size.ofBytes 2) .Read heldGlobal.protectedTags .SkipChildrenOfAccessed

def released := child.tree.releaseProtector tracker.global.nextPointerTag heldGlobal.protectedTags

theorem release_read_complete : releaseRead.status = .Completed := by cbv

theorem release_complete : released.status = .Released := by cbv

theorem actual_release : child.tree.releaseProtector tracker.global.nextPointerTag heldGlobal.protectedTags =
    ⟨released.tree,.Released⟩ := by
  change released = ⟨released.tree,.Released⟩
  cases result : released with
  | mk next status =>
    have good : status = .Released := by simpa only [result] using release_complete
    cases good
    rfl

/-- Only a tracker projection of the actual shared statement's output. -/
theorem actual_tracker (span : PreparedContracts.FixedSpanQuery) (updated : Allocation Provenance BorrowTree) :
    (S05ZeroCellActualCallSharedStmt.postMachine span updated).borrowTracker = some postSharedTracker := rfl

end DuplicatePrefix.S05ZeroCellActualCallLenReturn.PureTree

namespace DuplicatePrefix.S05ZeroCellActualCallLenReturn.ThreadFields
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.Concurrency
open Miri.TreeBorrows
open S05ZeroCellJointPacket (before)
open S05ZeroCellActualCallParameters
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

def initialThread : ThreadRecord := before.threads.threads[0]'(by change 0 < 1; decide)
def thread : ThreadRecord := {initialThread with topUserRelevantFrame := some 0}

theorem initial_active : before.threads.activeThread? = some initialThread := rfl

theorem raw_active : (RawRootInvocation.machine #[] before).threads.activeThread? = some thread := by
  have active : (CallEntryFacts.freshRoot before).1.threads.activeThread? = some initialThread := initial_active
  simpa only [RawRootInvocation.machine,Array.size_empty,thread] using
    PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 initialThread 0 active

/-- Only threads projections of the actual installed, ticked and allocated
machine. The abstract allocation and all metadata remain unexpanded. -/
theorem active (span : PreparedContracts.FixedSpanQuery) (updated : Allocation Provenance BorrowTree) :
    (S05ZeroCellActualCallSharedStmt.postMachine span updated).threads.activeThread? = some thread := by
  change (S05ZeroCellActualCallSharedStmt.current span updated).threads.activeThread? = some thread
  unfold S05ZeroCellActualCallSharedStmt.current
  rw [(RootZeroInvocationState.tick_fields options remaining span
    (S05ZeroCellActualCallInit.installed span updated).machine).2.2.2.1]
  change (RawRootInvocation.machine #[] before).threads.activeThread? = some thread
  exact raw_active

theorem cache : thread.topUserRelevantFrame = some 0 := rfl

end
end DuplicatePrefix.S05ZeroCellActualCallLenReturn.ThreadFields

/-! Same closed call, from the proved shared expression through the len helper's
return. The only new semantic calculations are the actual helper argument's
Read/protected child and protector release. All configuration and external
metadata conditions remain those of the preceding actual-call trace. -/
namespace DuplicatePrefix.S05ZeroCellActualCallLenReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures
open Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend
open S05ZeroCellActualCallParameters S05ZeroCellJointPacket
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option linter.unusedSimpArgs false
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

def finalTree (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag) (offset len : UInt64) :=
  let registered := TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag
  let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered.protectedTags .VisitChildrenOfAccessed
  (read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true).tree

/-- Actual diagnostic len argument installation; every borrow completion is internal. -/
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
    (treeEq : entry.allocation.extra = PureTree.tree)
    (parentEq : exprTag = PureTree.parent)
    (nextEq : tracker.global.nextPointerTag = PureTree.tracker.global.nextPointerTag)
    (protectedEq : tracker.global.protectedTags = PureTree.tracker.global.protectedTags)
    (offsetEq : offset = 0) (lenEq : len = 2)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (valid : 1 < frame.locals.size)
    (body : frame.body = LenHelper.body.body)
    (identity : frame.bodyIdentity = LenHelper.body.identity)
    (callee : frame.functionInstance = LenHelper.resolved.callee)
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
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let output := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let finalTree := finalTree entry.allocation.extra tracker exprTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    LenInstall.action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) value
      (Storage.withCurrent frames frame machine) =
      .ok (1,1) (Storage.withCurrent frames
        (TypedBorrowSteps.registeredFrame (LenInstall.resultFrame frame valid output) borrowFrame id tracker.global.nextPointerTag) resultMachine) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (Provenance.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
  let cache := LenInstall.cacheFrame frame valid
  have cacheValid : 1 < cache.locals.size := by simpa [cache,LenInstall.cacheFrame,LenInstall.spanFrame,LocalOperands.cachedLayoutFrame] using valid
  let live := RootArgumentEntry.liveFrame cache 1 cacheValid
  have liveValid : 1 < live.locals.size := by simpa [live,RootArgumentEntry.liveFrame] using cacheValid
  have cached : live.locals[1].layout = some SharedReferenceMetadata.sharedLayout := by
    simp [live,RootArgumentEntry.liveFrame,cache,LenInstall.cacheFrame,LocalOperands.cachedLayoutFrame,LenHelper.rawLayout]
  let copied := LenArgumentCopy.copiedFrame live 1 value liveValid
  have postValid : 1 < copied.locals.size := by simpa [copied,LenArgumentCopy.copiedFrame] using liveValid
  have postLive : copied.locals[1].value = .live (.immediate value) := by simp [copied,LenArgumentCopy.copiedFrame]
  have postCached : copied.locals[1].layout = some SharedReferenceMetadata.sharedLayout := by
    simpa [copied,LenArgumentCopy.copiedFrame] using cached
  let read := entry.allocation.extra.performBorrowAccessRange (.concrete exprTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed
  let child := read.tree.newChild (Size.ofBytes offset) (.concrete exprTag) tracker.global.nextPointerTag
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true
  have readFacts : read.status = .Completed ∧ read.tree = PureTree.read.tree := by
    simpa only [read,treeEq,parentEq,nextEq,offsetEq,lenEq,protectedEq,TypedBorrowSteps.registeredGlobal,
      PureTree.read,PureTree.heldGlobal,ReferenceBorrowDriver.allocatedTracker,TypedRetagGeneric.allocatedGlobal,Size.ZERO,Size.ofBytes] using And.intro PureTree.read_complete (Eq.refl PureTree.read.tree)
  have childDone : child.outcome = .ok () := by
    dsimp only [child]
    rw [readFacts.2]
    simpa only [parentEq,nextEq,offsetEq,lenEq,PureTree.child,Size.ZERO,Size.ofBytes] using PureTree.child_complete
  have childComplete := GeneralBorrowFreshReborrowStages.child_complete child childDone
  have info := RootReferenceInfo.facts options remaining span ctx true
  have validated := ProtectedReferenceValidator.positive options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    SharedReferenceMetadata.sharedLayout .Not .FnEntry (sharedPolicy true) frozenRead
    rfl (by decide +kernel) (shared_initial true) shared_entry_policy
    info.shape info.pointeeQuery info.unpin info.unsafeUnpin info.frozen info.dereference
    info.sized info.readable "&[u8]" info.named info.classified
    id entry base offset len exprTag positive nonzero signedFits bounds frames copied machine tracker enabled mode
    borrowFrame frameBorrow fresh 1 postValid postLive postCached ghost shallow cachedAddress present race read.tree child.tree
    rfl readFacts.1 childComplete metadata notConstructed
  have checked := LenArgumentCopy.copy_with_nested_validation options limits remaining span debugOff frames live machine
    1 .uninit value liveValid (by simp [live,RootArgumentEntry.liveFrame]) cached noClocks ghost shallow
    (LocalPlaces.localRuntimePlace frames.size live 1 SharedReferenceMetadata.sharedLayout).stackView rfl _
    (by rw [validationEq]; exact validated)
  apply LenInstall.install_of_copy options limits remaining span debugOff frames frame machine value valid body identity callee
    uncached dead noClocks ghost _
  simpa only [child,read,finalTree,copied,live,cache,LenArgumentCopy.copiedFrame,LenInstall.resultFrame,LenInstall.cacheFrame,
    LenInstall.spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame,
    TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,Array.getElem_set_self,Array.set_set] using checked


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
    (treeEq : entry.allocation.extra = PureTree.tree)
    (parentEq : exprTag = PureTree.parent)
    (nextEq : tracker.global.nextPointerTag = PureTree.tracker.global.nextPointerTag)
    (protectedEq : tracker.global.protectedTags = PureTree.tracker.global.protectedTags)
    (offsetEq : offset = 0) (lenEq : len = 2)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (valid : 1 < frame.locals.size)
    (body : frame.body = LenHelper.body.body)
    (identity : frame.bodyIdentity = LenHelper.body.identity)
    (callee : frame.functionInstance = LenHelper.resolved.callee)
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
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let output := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let finalTree := finalTree entry.allocation.extra tracker exprTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (LenInstall.action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) value)
      (Storage.withCurrent frames frame machine) =
      .ok (1,1) (Storage.withCurrent frames
        (TypedBorrowSteps.registeredFrame (LenInstall.resultFrame frame valid output) borrowFrame id tracker.global.nextPointerTag) resultMachine) := by
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


private theorem actual_entry
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
    (treeEq : entry.allocation.extra = PureTree.tree)
    (parentEq : exprTag = PureTree.parent)
    (nextEq : tracker.global.nextPointerTag = PureTree.tracker.global.nextPointerTag)
    (protectedEq : tracker.global.protectedTags = PureTree.tracker.global.protectedTags)
    (offsetEq : offset = 0) (lenEq : len = 2)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
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
    (notConstructed : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView current)).entries.any (·.value.ty == 4) = false) :
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
  let cfg := config options remaining span
  let state := Storage.withCurrent frames caller machine
  let destination := (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView
  let frame := LenEntry.rawFrame options state destination
  let postMachine := (LenPush.completed options.userRelevantCrates state destination current).machine
  have size : frame.locals.size = 3 := LenEntry.raw_size options state destination
  have valid1 : 1 < frame.locals.size := by rw [size];decide
  have postTracked : postMachine.borrowTracker = some tracker := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact enabled
  have postGhost : postMachine.user.payload.ghost = false := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact ghost
  have postShallow : postMachine.user.payload.validation = .Shallow := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact shallow
  have postAddress : postMachine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact cachedAddress
  have postPresent : postMachine.memory.live.find? (fun row => row.1 == id) = some (id,entry) := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact present
  have postRace : postMachine.dataRace = none := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact race
  have frameBorrow : frame.extra.borrowTracker = some {} := by
    simp [frame,LenEntry.rawFrame,LenFrame.rawFrame,LenPush.fresh,CallEntryFacts.freshRoot,state,Storage.withCurrent,enabled]
  have frameRace : frame.extra.dataRace = none := by
    simp [frame,LenEntry.rawFrame,LenFrame.rawFrame,LenPush.fresh,CallEntryFacts.freshRoot,state,Storage.withCurrent,race]
  have made := scoped_install_data options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len exprTag positive nonzero signedFits (frames.push caller) frame postMachine
    tracker postTracked {} frameBorrow fresh treeEq parentEq nextEq protectedEq offsetEq lenEq bounds valid1 rfl rfl rfl rfl rfl frameRace postGhost postShallow
    postAddress postPresent postRace metadata notConstructed
  let output := (RetagReferencePlace.sliceValue cfg.access.runtime.base
    (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
  let af := TypedBorrowSteps.registeredFrame (LenInstall.resultFrame frame valid1 output) {} id tracker.global.nextPointerTag
  have afSize : af.locals.size = 3 := by
    simpa only [af,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,LenInstall.resultFrame,
      LenInstall.cacheFrame,LenInstall.spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame,Array.size_set] using size
  have afValid : 0 < af.locals.size := by rw [afSize];decide
  have afDead : af.locals[0].value = .dead := by
    simp [af,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,LenInstall.resultFrame,
      LenInstall.cacheFrame,LenInstall.spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame,
      Array.getElem_set,frame,LenEntry.rawFrame,LenFrame.rawFrame,Frame.create]
  have afRace : af.extra.dataRace = none := by
    simpa only [af,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,LenInstall.resultFrame,LenInstall.cacheFrame,LenInstall.spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame] using frameRace
  exact LenEntry.actual_entry_of_install options limits remaining span debugOff frames caller machine tracker enabled _
    localId valid old live cached noClocks race ghost shallow thread index current active top presentFrame _ _ made
    rfl rfl rfl afValid afDead afRace



def source : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
  {S05ZeroCellActualCallSharedStmt.entry with allocation :=
    S05ZeroCellActualCallSharedStmt.entry.allocation.setExtra PureTree.tree}

private theorem environment (span : PreparedContracts.FixedSpanQuery) (updated : Allocation Provenance BorrowTree) :
    let machine := S05ZeroCellActualCallSharedStmt.postMachine span updated
    machine.user.addresses = before.user.addresses ∧ machine.user.payload.ghost = false ∧
    machine.user.payload.validation = .Shallow ∧ machine.dataRace = none ∧
    machine.user.payload.payload.user.types = PreparedReflection.actual.types ∧
    machine.user.payload.payload.user.backend = .none ∧ machine.threads.fixedScheduling = true := by
  unfold S05ZeroCellActualCallSharedStmt.postMachine S05ZeroCellActualCallSharedStmt.current
    RootZeroCompleteState.tick SourceControl.accounted
  rw [(actual_fields options () (remaining+1) span).terminators]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem source_present (span : PreparedContracts.FixedSpanQuery) (updated : Allocation Provenance BorrowTree) :
    (S05ZeroCellActualCallSharedStmt.postMachine span updated).memory.live.find? (fun row => row.1 == sourceId) =
      some (sourceId,source) := by
  exact MemoryCopyBridge.live_lookup_replaced
    (S05ZeroCellActualCallSharedStmt.current span updated).memory sourceId source


/-- The same actual call through the len helper's return. All witness machines
are retained, including the exact source pop expression rather than only its
memory/tracker projections. -/
theorem initializes_through_len (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator) (compare : PreparedContracts.SourceComparator) :
    let cfg := config options (remaining+1) span
    ∃ updated : Allocation Provenance BorrowTree, ∃ finished : RootState,
      initializationResult span = .ok () (S05ZeroCellActualCallInit.installed span updated) ∧
      SuccessfulTrace.Trace cfg limits (S05ZeroCellActualCallInit.installed span updated) finished ∧
      (S05ZeroCellActualCallInit.installed span updated).stack.frames.size = 1 ∧ finished.stack.frames.size = 1 ∧
      finished.stack.currentFrame?.map (·.location) = some (.mir ⟨3,0⟩) ∧
      (finished.stack.currentFrame?.bind fun frame => frame.locals[11]?) =
        some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 2)))),some RootCompilerFacts.usizeLayout⟩ ∧
      ∃ caller : CompilerFrameContext.ActualFrame, ∃ valid : 11 < caller.locals.size,
      ∃ helper : CompilerFrameContext.ActualFrame,
      ∃ doneMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      ∃ releasedMemory : MemoryState Provenance BorrowTree MiriMemoryKind,
      ∃ held : MachineHooks.BorrowState, ∃ loan : FrameState, ∃ thread : ThreadRecord,
        finished = Storage.withCurrent #[]
          {PtrMetadataExecution.writeFrame caller 11 (.scalar (.fromScalarInt (.ofUInt64 2))) valid with location := .mir ⟨3,0⟩}
          (PtrMetadataReturn.poppedMachine #[] caller helper
            (ActualPopPlan.released (PtrMetadataReturn.accountedMachine options remaining span doneMachine)
              releasedMemory held loan) (thread.topUserRelevantFrame.getD 1)) ∧
        doneMachine.memory = RetagEntry.updatedMemory (S05ZeroCellActualCallSharedStmt.postMachine span updated).memory
          sourceId source PureTree.child.tree ∧
        doneMachine.borrowTracker = some held ∧
        held = TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker PureTree.postSharedTracker PureTree.fresh)
          PureTree.tracker.global.nextPointerTag ∧
        loan = ({} : FrameState).addProtector sourceId PureTree.tracker.global.nextPointerTag ∧
        releasedMemory = StackPopRelease.commitTree doneMachine.memory sourceId
          {source with allocation := source.allocation.setExtra PureTree.child.tree} PureTree.released.tree ∧
        doneMachine.user.addresses = (S05ZeroCellActualCallSharedStmt.postMachine span updated).user.addresses ∧
        doneMachine.user.payload.payload.user.types = (S05ZeroCellActualCallSharedStmt.postMachine span updated).user.payload.payload.user.types ∧
        doneMachine.user.payload.payload.user.runtime.extras = (S05ZeroCellActualCallSharedStmt.postMachine span updated).user.payload.payload.user.runtime.extras ∧
        doneMachine.user.payload.ghost = false ∧ doneMachine.user.payload.validation = .Shallow ∧ doneMachine.dataRace = none ∧
        doneMachine.threads.activeThread? = some thread ∧
        GeneralBorrowForestMixedLenBeforeReturn.ReturnFacts options remaining span helper doneMachine 2
          (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete sourceId PureTree.tracker.global.nextPointerTag) (Size.ofBytes 4096)) 2 SharedReferenceMetadata.sharedLayout).imm ∧
        GeneralBorrowForestMixedLenBeforeReturn.RootCache #[] doneMachine ∧
        ∃ original : CompilerFrameContext.ActualFrame, ∃ valid12 : 12 < original.locals.size,
          GenericFunctionEntryPrefix.Shape ((S05ZeroCellActualCallInit.installed span updated).stack.frames[0]'(by change 0 < 1; decide)) original 1 ∧
          ∃ validCall : 11 < (CopyHelperSteps.advance (ActualLocalCopy.written original 12 (RootReferenceInfo.layout true) valid12
              (S05ZeroCellActualCallSharedStmt.value span).imm) ⟨2,11⟩).locals.size,
            caller = cachedCaller (CopyHelperSteps.advance (ActualLocalCopy.written original 12 (RootReferenceInfo.layout true) valid12
              (S05ZeroCellActualCallSharedStmt.value span).imm) ⟨2,11⟩) validCall := by
  obtain ⟨updated,site,v12,init,sharedStep,initTrace,shape,depth,endDepth,located⟩ :=
    S05ZeroCellActualCallSharedStmt.initializes_and_shared span cmp compare
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span rfl rfl
  let raw := RawRootInvocation.root before place profile.2.2.2.1
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete sourceId S05ZeroCellActualCallSharedStmt.PureTree.initialGlobal.nextPointerTag)
      (Size.ofBytes 4096)) 2 ActualReferenceMetadata.reference).imm
  let start := PositiveRootInstalledFrame.installed raw adjusted 1 {} sourceId
    S05ZeroCellActualCallSharedStmt.PureTree.initialGlobal.nextPointerTag destinationId
    S05ZeroCellActualCallSharedStmt.PureTree.tracker9.global.nextPointerTag
  change GenericFunctionEntryPrefix.Shape start site 1 at shape
  obtain ⟨body0,identity0,callee0,cont0,place0,va0,clocks0,borrow0,location0⟩ :=
    PositiveRootInstalledFrame.metadata raw adjusted 1 {} sourceId
      S05ZeroCellActualCallSharedStmt.PureTree.initialGlobal.nextPointerTag destinationId
      S05ZeroCellActualCallSharedStmt.PureTree.tracker9.global.nextPointerTag
  let frame := CopyHelperSteps.advance
    (ActualLocalCopy.written site 12 (RootReferenceInfo.layout true) v12
      (S05ZeroCellActualCallSharedStmt.value span).imm) ⟨2,11⟩
  let beforeMachine := S05ZeroCellActualCallSharedStmt.postMachine span updated
  let machine := PtrMetadataReturn.accountedMachine options remaining span beforeMachine
  let tracker := PureTree.postSharedTracker
  have body : frame.body = RootBody.reflected.body.body := shape.body.trans (body0.trans raw.body)
  have identity : frame.bodyIdentity = RootBody.reflected.body.identity := shape.identity.trans (identity0.trans raw.identity)
  have callee : frame.functionInstance = RootBody.reflected.functionInstance := shape.callee.trans (callee0.trans raw.callee)
  have clocks : frame.extra.dataRace = none := (congrArg (·.dataRace) shape.extra).trans (clocks0.trans raw.noClocks)
  have v11 : 11 < frame.locals.size := by
    simpa only [frame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.size_set,shape.size] using (show 11 < 25 by decide)
  have valid12 : 12 < frame.locals.size := by
    simpa only [frame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.size_set,shape.size] using (show 12 < 25 by decide)
  have slot11 : site.locals[11] = ⟨.live (.immediate .uninit),none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (by rw [shape.size]; decide)).symm.trans shape.slot11)
  have live : frame.locals[11].value = .live (.immediate .uninit) := by
    simpa [frame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using congrArg LocalState.value slot11
  have uncached : frame.locals[11].layout = none := by
    simpa [frame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using congrArg LocalState.layout slot11
  have valueLive : frame.locals[12].value = .live (.immediate (S05ZeroCellActualCallSharedStmt.value span).imm) := by
    simp [frame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set_self,RootReferenceInfo.layout]
  have valueCached : frame.locals[12].layout = some SharedReferenceMetadata.sharedLayout := by
    simp [frame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set_self,RootReferenceInfo.layout]
  have env := environment span updated
  have tracked : machine.borrowTracker = some tracker := PureTree.actual_tracker span updated
  have cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == sourceId) = some ⟨sourceId,4096⟩ := by
    unfold machine PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    change beforeMachine.user.addresses.baseAddr.find? _ = _
    rw [env.1]
    exact source_cached
  have present : machine.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,source) := source_present span updated
  let caller := cachedCaller frame v11
  let destination := (LocalPlaces.localRuntimePlace 0 caller 11 RootCompilerFacts.usizeLayout).stackView
  let state := Storage.withCurrent #[] caller machine
  have ghost : machine.user.payload.ghost = false := by rw [PtrMetadataReturn.accounted_ghost]; exact env.2.1
  have shallow : machine.user.payload.validation = .Shallow := by rw [PtrMetadataReturn.accounted_validation]; exact env.2.2.1
  have race : machine.dataRace = none := env.2.2.2.1
  have backend : machine.user.payload.payload.user.backend = .none := by
    unfold machine PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact env.2.2.2.2.2.1
  have types : machine.user.payload.payload.user.types = PreparedReflection.actual.types := by
    unfold machine PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact env.2.2.2.2.1
  have active : machine.threads.activeThread? = some ThreadFields.thread := ThreadFields.active span updated
  have top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates state destination).stack
      ThreadFields.thread.topUserRelevantFrame = some 0 := by simp [FrameRelevance.top,ThreadFields.cache]
  have current : (LenPush.pushed options.userRelevantCrates state destination).stack.frames[0]? = some caller := by
    simp [LenPush.pushed,state,Storage.withCurrent]
  have postTypes : (LenPush.completed options.userRelevantCrates state destination caller).machine.user.payload.payload.user.types =
      PreparedReflection.actual.types := by
    simp only [LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact types
  have metadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates state destination caller)).metadata =
      PreparedReflection.actual.runtime := by change (LenPush.completed _ _ _ _).machine.user.payload.payload.user.types.metadata = _; rw [postTypes]; rfl
  have notConstructed : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates state destination caller)).entries.any
      (·.value.ty == 4) = false := by change ((LenPush.completed _ _ _ _).machine.user.payload.payload.user.types.entries.any _) = _; rw [postTypes]; decide +kernel
  have callerValid : 11 < caller.locals.size := by simpa [caller,cachedCaller,LocalPlaces.cachePlaceLayout] using v11
  have callerLive : caller.locals[11].value = .live (.immediate .uninit) := by simpa [caller,cachedCaller,LocalPlaces.cachePlaceLayout] using live
  have callerCached : caller.locals[11].layout = some RootCompilerFacts.usizeLayout := by simp [caller,cachedCaller,LocalPlaces.cachePlaceLayout]
  have entered := actual_entry options limits remaining span ctx rfl cmp remaining remaining rfl rfl
    sourceId source 4096 0 2 PureTree.parent (by decide) (by decide) (by decide)
    #[] caller machine tracker tracked PureTree.fresh rfl rfl rfl rfl rfl rfl (by decide)
    11 callerValid .uninit callerLive callerCached clocks ghost shallow cachedAddress present race
    ThreadFields.thread 0 caller active top current metadata notConstructed
  have called := LenUncachedFrontend.call_uncached_of_entry options limits (remaining+1) 999999 rfl span rfl
    #[] frame machine (S05ZeroCellActualCallSharedStmt.value span).imm body identity callee rfl compare cmp
    valid12 valueLive valueCached v11 uncached clocks race backend ghost _ _ entered
  let childTree := finalTree source.allocation.extra tracker PureTree.parent 0 2
  let helperValue := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete sourceId tracker.global.nextPointerTag) (Size.ofBytes 4096)) 2 SharedReferenceMetadata.sharedLayout).imm
  let helper := LenEntryShape.initialized options state destination helperValue true sourceId tracker.global.nextPointerTag
  let post := (LenPush.completed options.userRelevantCrates state destination caller).machine
  let enteredMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine post tracker PureTree.fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker PureTree.fresh) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory post.memory sourceId source childTree}
  have called' : Call.evalCallTerminator (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      () limits.callDispatch LenCallSource.callTerminator (Storage.withCurrent #[] frame machine) =
      .ok () (Storage.withCurrent #[caller] helper enteredMachine) := by
    simpa [helper,helperValue,childTree,enteredMachine,post,LenEntryShape.initialized,caller,state,destination,
      S05ZeroCellActualCallSharedStmt.value,PureTree.parent,UInt64.add_zero] using called
  have unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false := by
    unfold beforeMachine S05ZeroCellActualCallSharedStmt.postMachine S05ZeroCellActualCallSharedStmt.current RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    rfl
  have noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0 := by
    unfold beforeMachine S05ZeroCellActualCallSharedStmt.postMachine S05ZeroCellActualCallSharedStmt.current RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    rfl
  have accounting := SourceControl.before_terminator (config options (remaining+1) span) limits ()
    (Storage.withCurrent #[] frame beforeMachine) (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc env.2.2.2.2.2.2
  have accounting' : (ExecutionMachine.stepHooks (config options (remaining+1) span) limits).beforeTerminator ()
      (Storage.withCurrent #[] frame beforeMachine) = (Storage.withCurrent #[] frame machine,.ok ()) := by
    simpa only [machine,PtrMetadataReturn.accountedMachine,SourceControl.accounted,Storage.withCurrent] using accounting
  let block := RootBody.reflected.body.body.basicBlocks[2]'(by decide +kernel)
  have blockAt : frame.body.basicBlocks[2]? = some block := by rw [body]; simp [block]
  have entryStep : ExecutionMachine.step (config options (remaining+1) span) limits ()
      (Storage.withCurrent #[] frame beforeMachine) = (Storage.withCurrent #[caller] helper enteredMachine,.ok true) := by
    apply GenericCallStages.source_step (config options (remaining+1) span) limits ()
      (Storage.withCurrent #[] frame beforeMachine) (Storage.withCurrent #[] frame machine) _ frame ⟨2,12⟩ block
      LenHelper.resolved.function #[LenEvaluateCall.argument] ⟨11,#[]⟩ (some 3) .Continue LenCallFrontend.sourceKind LenCallFrontend.fnSpan
      (by simp [Storage.withCurrent,Stack.currentFrame?]) rfl blockAt (by with_unfolding_all rfl)
      LenCallFrontend.source_call accounting' called'
    simp [Storage.withCurrent]
  have capacity : source.allocation.extra.locations.size = source.allocation.byteSize := by cbv
  obtain ⟨result,doneMachine,properties,details,rootCache⟩ :=
    LenBodyFromEntry.before_return_full_data options limits remaining 999999 rfl span ctx rfl cmp remaining remaining rfl rfl
      sourceId source 4096 0 2 PureTree.parent (by decide) (by decide) (by decide) (by decide)
      #[] frame machine tracker tracked rfl PureTree.fresh childTree capacity v11 live uncached clocks
      ghost shallow cachedAddress present race ThreadFields.thread 0 caller active top current metadata notConstructed
      body identity callee rfl compare valid12 valueLive valueCached backend beforeMachine rfl unchecked noGc
      env.2.2.2.2.2.2 entryStep
  rcases properties with ⟨bodyTrace,helperLocation,retval,frameTracked,helperRace,returnPlace,continuation,varargs,
    memoryEq,doneTracked,doneGhost,doneShallow,doneRace,doneAddresses,doneTypes,doneExtras⟩
  let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker PureTree.fresh)
    tracker.global.nextPointerTag
  let loan := ({} : FrameState).addProtector sourceId tracker.global.nextPointerTag
  have childEq : childTree = PureTree.child.tree := rfl
  have complete : childTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags =
      ⟨PureTree.released.tree,.Released⟩ := by
    simpa only [childEq,held,tracker,PureTree.tracker,PureTree.heldGlobal,
      TypedBorrowSteps.registeredTracker,ReferenceBorrowDriver.allocatedTracker,TypedBorrowSteps.registeredGlobal]
      using PureTree.actual_release
  let inside : LocalAllocation Provenance BorrowTree MiriMemoryKind := {source with allocation := source.allocation.setExtra childTree}
  have found : doneMachine.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,inside) := by
    rw [memoryEq]
    exact StackPopRelease.lookup_commit_same beforeMachine.memory sourceId source childTree
  let releasedMemory := StackPopRelease.commitTree doneMachine.memory sourceId inside PureTree.released.tree
  have plan : StackPopRelease.Plan held.global.protectedTags loan.protectedTags.toList doneMachine.memory releasedMemory := by
    exact StackPopRelease.Plan.live sourceId tracker.global.nextPointerTag inside PureTree.released.tree [] doneMachine.memory
      _ found complete (.nil _)
  have valid0 : 0 < result.locals.size := by rw [details.size]; decide
  have returnedCell : result.locals[0]'valid0 =
      ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 2)))),some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans retval)
  have immediate : ∀ slot ∈ result.locals, ∀ memory, slot.value ≠ .live (.indirect memory) := by
    apply PtrMetadataComplete.all_direct_three result.locals details.size
    · simp only [retval,Option.map_some,PtrMetadataComplete.isDirect]
    · simp only [details.argument,Option.map_some,PtrMetadataComplete.isDirect]
    · have known := congrArg (Option.map PtrMetadataComplete.isDirect) details.dead2
      simpa only [Option.map_map,Function.comp_def,Option.map_some,PtrMetadataComplete.isDirect] using known
  obtain ⟨thread,threadActive⟩ := details.active
  have returned := LenReturn.step_with_plan options limits remaining span rfl remaining rfl #[] caller result doneMachine 2
    details.body helperLocation valid0 (congrArg LocalState.value returnedCell) (congrArg LocalState.layout returnedCell)
    helperRace 11 callerValid callerLive callerCached clocks returnPlace 3 .Continue continuation immediate varargs
    held loan doneTracked frameTracked releasedMemory plan thread threadActive details.unchecked details.noGc details.fixed
    doneGhost doneShallow
  let final : RootState := Storage.withCurrent #[]
    {PtrMetadataExecution.writeFrame caller 11 (.scalar (.fromScalarInt (.ofUInt64 2))) callerValid with location := .mir ⟨3,0⟩}
    (PtrMetadataReturn.poppedMachine #[] caller result
      (ActualPopPlan.released (PtrMetadataReturn.accountedMachine options remaining span doneMachine) releasedMemory held loan)
      (thread.topUserRelevantFrame.getD 1))
  have returned' : ExecutionMachine.step (config options (remaining+1) span) limits ()
      (Storage.withCurrent #[caller] result doneMachine) = (final,.ok true) := by
    simpa [final,ActualReferenceContext.config] using returned
  refine ⟨updated,final,init,?_,depth,rfl,?_,?_,caller,callerValid,result,doneMachine,releasedMemory,held,loan,thread,?_⟩
  · exact SuccessfulTrace.append initTrace (SuccessfulTrace.append bodyTrace (.next returned' (.refl _)))
  · simp only [final,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,Option.map_some]
  · simp [final,Storage.withCurrent,Stack.currentFrame?,PtrMetadataExecution.writeFrame,callerCached]
  · refine ⟨rfl,?_,doneTracked,rfl,rfl,?_,doneAddresses,doneTypes,doneExtras,doneGhost,doneShallow,doneRace,threadActive,?_,rootCache,site,v12,shape,v11,rfl⟩
    · simpa only [childEq] using memoryEq
    · simp only [releasedMemory,inside,childEq]
    · simpa only [tracker,PureTree.tracker,UInt64.add_zero] using details

end
end DuplicatePrefix.S05ZeroCellActualCallLenReturn
