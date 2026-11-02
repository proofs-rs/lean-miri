import duplicate_prefix.S05ZeroCellActualCallToLen
import duplicate_prefix.RootReferenceBorrow
import duplicate_prefix.RootZeroInvocationState
import duplicate_prefix.GeneralBorrowFreshAnchor
import Init.Internal.Order.While

namespace DuplicatePrefix.S05ZeroCellActualCallSharedStmt.PureTree
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open S05ZeroCellTypedGeneratedPrefix
open S05ZeroCellJointPacket (sourceId destinationId)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

def initialGlobal : GlobalState :=
  {nextPointerTag := tag 8,rootPointerTags := #[(sourceId,tag 1),(destinationId,tag 7)]}
theorem fresh8 : initialGlobal.nextPointerTag.value < 18446744073709551615 := by decide +kernel

def afterArgument : GlobalState := TypedRetagGeneric.protectedGlobal initialGlobal fresh8
def tracker9 : MachineHooks.BorrowState := ⟨afterArgument,.Default⟩
theorem fresh9 : tracker9.global.nextPointerTag.value < 18446744073709551615 := by decide +kernel

/-- The bool registration's actual allocator/protector result. No literal
replacement of its next tag is used in the two operations below. -/
def global : GlobalState := TypedBorrowSteps.registeredGlobal
  (ReferenceBorrowDriver.allocatedTracker tracker9 fresh9) tracker9.global.nextPointerTag

def sourceTree : BorrowTree := S05ZeroCellActualCallInit.PureTree.child.tree
def read := sourceTree.performBorrowAccessRange (.concrete initialGlobal.nextPointerTag) Size.ZERO
  (Size.ofBytes 2) .Read global.protectedTags .VisitChildrenOfAccessed
def child := read.tree.newChild Size.ZERO (.concrete initialGlobal.nextPointerTag) global.nextPointerTag
  (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshAnchor.sharedState) .Frozen false

theorem read_complete : read.status = .Completed := by cbv

theorem child_complete : child.outcome = .ok () := by cbv

/-- Projection identity only: neither the whole state nor the abstract bool
allocation is evaluated. Tick changes the control/user fields, not this tracker. -/
theorem actual_tracker (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (updated : Allocation Provenance BorrowTree) :
    (RootZeroCompleteState.tick options remaining span
      (S05ZeroCellActualCallInit.installed span updated).machine).borrowTracker = some ⟨global,.Default⟩ := by
  unfold RootZeroCompleteState.tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl

end DuplicatePrefix.S05ZeroCellActualCallSharedStmt.PureTree


namespace DuplicatePrefix.S05ZeroCellActualCallSharedStmt
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext S05ZeroCellActualCallParameters S05ZeroCellJointPacket
open RootReferenceInfo
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def current (span : PreparedContracts.FixedSpanQuery) (updated : Allocation Provenance BorrowTree) :=
  RootZeroCompleteState.tick options remaining span (S05ZeroCellActualCallInit.installed span updated).machine

def entry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
  {sourceEntry with allocation := sourceEntry.allocation.setExtra PureTree.sourceTree}

private theorem present (span : PreparedContracts.FixedSpanQuery) (updated : Allocation Provenance BorrowTree) :
    (current span updated).memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,entry) := by
  unfold current
  rw [(RootZeroInvocationState.tick_fields options remaining span (S05ZeroCellActualCallInit.installed span updated).machine).1]
  let args := S05ZeroCellActualCallInit.argumentMachine
  have initial : args.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,entry) :=
    StackPopRelease.lookup_commit_same (RawRootInvocation.machine #[] before).memory sourceId sourceEntry PureTree.sourceTree
  let boolTag := (args.borrowTracker.get (by rfl)).global.nextPointerTag
  have middle := StackPopRelease.lookup_commit_other args.memory destinationId sourceId destinationEntry entry
    (PhysicalMachineWrite.slotTree (S05ZeroCellTypedGeneratedPrefix.tag 7) boolTag 1 false)
    distinct_ids initial
  have final := StackPopRelease.lookup_commit_other
    (StackPopRelease.commitTree args.memory destinationId destinationEntry
      (PhysicalMachineWrite.slotTree (S05ZeroCellTypedGeneratedPrefix.tag 7) boolTag 1 false))
    destinationId sourceId ⟨destinationEntry.kind,updated⟩ entry updated.extra distinct_ids middle
  have same : updated.setExtra updated.extra = updated := by cases updated; rfl
  with_unfolding_all simpa only [same,S05ZeroCellActualCallInit.installed,ReturnProtection.borrowedState,CanonicalCopy.replaceAllocation,
    Storage.withCurrent,ReferenceBorrowDriver.allocatedMachine,TypedBorrowSteps.registeredMachine,StackPopRelease.commitTree,
    RetagEntry.updatedMemory,args,boolTag,S05ZeroCellActualCallInit.argumentMachine,Option.get_some] using final

private theorem fresh : PureTree.global.nextPointerTag.value < 18446744073709551615 := by decide +kernel

def value (span : PreparedContracts.FixedSpanQuery) := RetagReferencePlace.sliceValue
  (config options remaining span).access.runtime.base
  (Pointer.new (.concrete sourceId PureTree.global.nextPointerTag) (Size.ofBytes 4096)) 2 (layout true)
def postMachine (span : PreparedContracts.FixedSpanQuery) (updated : Allocation Provenance BorrowTree) :=
  {ReferenceBorrowDriver.allocatedMachine (current span updated) ⟨PureTree.global,.Default⟩ fresh with
    memory := RetagEntry.updatedMemory (current span updated).memory sourceId entry PureTree.child.tree}
def after (span : PreparedContracts.FixedSpanQuery) (updated : Allocation Provenance BorrowTree)
    (site : CompilerFrameContext.ActualFrame) (valid : 12 < site.locals.size) : RootState :=
  Storage.withCurrent #[] (CopyHelperSteps.advance (ActualLocalCopy.written site 12 (layout true) valid (value span).imm) ⟨2,11⟩)
    (postMachine span updated)

/-- One actual shared-reference statement, appended to the same actual init and
structural prefix. Only the three independent metadata conditions are inputs. -/
theorem initializes_and_shared (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator) (source : PreparedContracts.SourceComparator) :
    let cfg := config options (remaining+1) span
    ∃ updated : Allocation Provenance BorrowTree, ∃ site : CompilerFrameContext.ActualFrame, ∃ valid : 12 < site.locals.size,
      initializationResult span = .ok () (S05ZeroCellActualCallInit.installed span updated) ∧
      ExecutionMachine.step cfg limits () (Storage.withCurrent #[] site (current span updated)) = (after span updated site valid,.ok true) ∧
      SuccessfulTrace.Trace cfg limits (S05ZeroCellActualCallInit.installed span updated) (after span updated site valid) ∧
      GenericFunctionEntryPrefix.Shape ((S05ZeroCellActualCallInit.installed span updated).stack.frames[0]'(by change 0 < 1; decide)) site 1 ∧
      (S05ZeroCellActualCallInit.installed span updated).stack.frames.size = 1 ∧ (after span updated site valid).stack.frames.size = 1 ∧
      (after span updated site valid).stack.currentFrame?.map (·.location) = some (.mir ⟨2,12⟩) := by
  obtain ⟨updated,site,init,initTrace,shape,depth,endDepth,located⟩ := S05ZeroCellActualCallToLen.initializes_to_len span cmp source
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span rfl rfl
  let machine := current span updated
  let tracker : MachineHooks.BorrowState := ⟨PureTree.global,.Default⟩
  have tracked : machine.borrowTracker = some tracker := PureTree.actual_tracker options remaining span updated
  let raw := RawRootInvocation.root before place profile.2.2.2.1
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete sourceId PureTree.initialGlobal.nextPointerTag) (Size.ofBytes 4096)) 2 ActualReferenceMetadata.reference).imm
  let start := PositiveRootInstalledFrame.installed raw adjusted 1 {} sourceId PureTree.initialGlobal.nextPointerTag
    destinationId PureTree.tracker9.global.nextPointerTag
  change GenericFunctionEntryPrefix.Shape start site 1 at shape
  obtain ⟨body0,identity0,callee0,cont0,place0,va0,clocks0,borrow0,location0⟩ :=
    PositiveRootInstalledFrame.metadata raw adjusted 1 {} sourceId PureTree.initialGlobal.nextPointerTag destinationId PureTree.tracker9.global.nextPointerTag
  have body := shape.body.trans (body0.trans raw.body)
  have identity := shape.identity.trans (identity0.trans raw.identity)
  have callee := shape.callee.trans (callee0.trans raw.callee)
  have clocks : site.extra.dataRace = none := (congrArg (·.dataRace) shape.extra).trans (clocks0.trans raw.noClocks)
  have v1 : 1 < site.locals.size := by rw [shape.size]; decide
  have v12 : 12 < site.locals.size := by rw [shape.size]; decide
  have sourceSlot := PositiveRootInstalledFrame.slot_option raw (RawRootInvocation.locals before place profile.2.2.2.1)
    adjusted 1 {} sourceId PureTree.initialGlobal.nextPointerTag destinationId PureTree.tracker9.global.nextPointerTag ⟨1,by decide⟩
  have sourceCell := Option.some.inj ((Array.getElem?_eq_getElem v1).symm.trans (shape.slot1.trans (by simpa using sourceSlot)))
  have destCell := Option.some.inj ((Array.getElem?_eq_getElem v12).symm.trans shape.slot12)
  have env : machine.user.addresses = before.user.addresses ∧ machine.user.payload.ghost = false ∧
      machine.user.payload.validation = .Shallow ∧ machine.dataRace = none ∧ machine.user.payload.payload.user.types = PreparedReflection.actual.types := by
    unfold machine current RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  have cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == sourceId) = some ⟨sourceId,4096⟩ := by rw [env.1]; exact source_cached
  have metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime := by rw [env.2.2.2.2]; rfl
  have notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false := by rw [env.2.2.2.2]; decide +kernel
  have info := RootReferenceInfo.facts options remaining span ctx true
  let cachedFrame := LocalPlaces.cachePlaceLayout site 12 (layout true) v12
  have vc1 : 1 < cachedFrame.locals.size := by simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using v1
  have vc12 : 12 < cachedFrame.locals.size := by simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using v12
  have query := RootReferenceFacts.compute_destination #[] site machine body identity callee true
  have destination := ActualLocalPlace.uncached options limits (remaining+1) span rfl #[] site machine
    12 (layout true) v12 (congrArg LocalState.layout destCell) info.sized query
  have baseEq : (config options (remaining+1) span).access.runtime.base = (config options remaining span).access.runtime.base := by
    rw [CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span,CanonicalConfigFacts.actual_access_runtime options () remaining span]
  have srcLive : cachedFrame.locals[1].value = .live (.immediate (PtrMetadataComplete.rawImmediate
      (.inl (Pointer.new (.concrete sourceId PureTree.initialGlobal.nextPointerTag) (Size.ofBytes 4096)))
      (config options (remaining+1) span).access.runtime.base 2)) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,adjusted,baseEq,
      PtrMetadataComplete.rawImmediate,RetagReferencePlace.sliceValue] using congrArg LocalState.value sourceCell
  have srcCached : cachedFrame.locals[1].layout = some ActualReferenceMetadata.reference := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set] using congrArg LocalState.layout sourceCell
  have sourcePlace := RootReferencePlace.actual_slice_place options limits (remaining+1) span rfl #[] cachedFrame machine
    1 (.inl (Pointer.new (.concrete sourceId PureTree.initialGlobal.nextPointerTag) (Size.ofBytes 4096))) 2 vc1 srcLive srcCached clocks env.2.1
  have liveDest : cachedFrame.locals[12].value = .live (.immediate .uninit) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using congrArg LocalState.value destCell
  have cacheDest : cachedFrame.locals[12].layout = some (layout true) := by simp [cachedFrame,LocalPlaces.cachePlaceLayout]
  let entered := RootReferenceRvalue.enter machine tracker true
  let activeTracker := {tracker with retagMode := RootReferenceInfo.mode true}
  let changed := {ReferenceBorrowDriver.allocatedMachine entered activeTracker fresh with
    memory := RetagEntry.updatedMemory machine.memory sourceId entry PureTree.child.tree}
  let written := RootReferenceWrite.written cachedFrame 12 (value span).imm vc12
  have childDone : PureTree.read.tree.newChild Size.ZERO (.concrete PureTree.initialGlobal.nextPointerTag) PureTree.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes 2) (RootReferenceInfo.initial true))
      (RootReferenceInfo.policy true).outsidePermission false = ⟨PureTree.child.tree,.ok ()⟩ :=
    GeneralBorrowFreshReborrowStages.child_complete PureTree.child PureTree.child_complete
  have writer := RootReferenceWrite.positive_cached options limits remaining span ctx rfl cmp true remaining remaining rfl rfl
    sourceId entry 4096 0 2 PureTree.initialGlobal.nextPointerTag (by decide) (by decide) (by decide) (by decide)
    #[] cachedFrame entered activeTracker rfl rfl fresh 12 .uninit vc12 liveDest cacheDest clocks env.2.1 env.2.2.1
    cached (present span updated) env.2.2.2.1 PureTree.read.tree PureTree.child.tree rfl PureTree.read_complete childDone metadata notConstructed
  have writer' : (ExecutionMachine.rvalueHooks (config options (remaining+1) span) limits).writeImmediate ()
      (PtrMetadataComplete.rawImmediate (.inl (Pointer.new (.concrete sourceId PureTree.initialGlobal.nextPointerTag) (Size.ofBytes 4096)))
        (config options (remaining+1) span).access.runtime.base 2)
      (LocalPlaces.localRuntimePlace 0 cachedFrame 12 (layout true)) (Storage.withCurrent #[] cachedFrame entered) =
      .ok () (Storage.withCurrent #[] written changed) := by
    simpa only [baseEq,PtrMetadataComplete.rawImmediate,RetagReferencePlace.sliceValue,value,UInt64.add_zero,
      written,changed,entered,RootReferenceRvalue.enter,activeTracker,tracker,ActualReferenceContext.config,Array.size_empty,
      ReferenceBorrowDriver.allocatedMachine,ReferenceBorrowDriver.allocatedTracker] using writer
  have expression := RootReferenceRvalue.of_write options limits (remaining+1) span true .Erased
    (.inl (Pointer.new (.concrete sourceId PureTree.initialGlobal.nextPointerTag) (Size.ofBytes 4096))) 2 ⟨1,#[.Deref]⟩ ⟨12,#[]⟩
    (LocalPlaces.localRuntimePlace 0 cachedFrame 12 (layout true)) (Storage.withCurrent #[] site machine) #[] cachedFrame machine
    tracker (ReferenceBorrowDriver.allocatedTracker activeTracker fresh) tracked env.2.2.1 rfl destination sourcePlace written changed rfl writer'
  have expression' : evalRvalueIntoPlace (ExecutionMachine.rvalueHooks (config options (remaining+1) span) limits) ()
      (.Ref .Erased (RootReferenceRvalue.borrowKind true) ⟨1,#[.Deref]⟩) ⟨12,#[]⟩ (Storage.withCurrent #[] site machine) =
      .ok () (Storage.withCurrent #[] (ActualLocalCopy.written site 12 (layout true) v12 (value span).imm) (postMachine span updated)) := by
    simpa only [written,changed,entered,activeTracker,tracker,RootReferenceRvalue.enter,RootReferenceWrite.written,
      ActualLocalCopy.written,cachedFrame,postMachine,machine,ActualReferenceContext.config,
      ReferenceBorrowDriver.allocatedMachine,ReferenceBorrowDriver.allocatedTracker] using expression
  have step := CopyHelperSteps.assign_of_actual_rvalue (config options (remaining+1) span) limits #[] site
    (ActualLocalCopy.written site 12 (layout true) v12 (value span).imm) machine (postMachine span updated)
    ⟨2,11⟩ ⟨12,#[]⟩ (.Ref .Erased (RootReferenceRvalue.borrowKind true) ⟨1,#[.Deref]⟩) shape.location
    (by simpa only [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using shape.location)
    (by rw [body]; exact RootReferenceFacts.statement true) expression'
  refine ⟨updated,site,v12,init,step,?_,shape,depth,rfl,?_⟩
  · exact SuccessfulTrace.append initTrace (.next step (.refl _))
  · simp only [after,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,Option.map_some,CopyHelperSteps.advance]

end
end DuplicatePrefix.S05ZeroCellActualCallSharedStmt
