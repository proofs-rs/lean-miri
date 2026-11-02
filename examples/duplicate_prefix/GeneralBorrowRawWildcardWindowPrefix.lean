import duplicate_prefix.GeneralBorrowRawWildcardWindowInitialize
import duplicate_prefix.GeneralBorrowRawWildcardWindowRuntime
namespace DuplicatePrefix.GeneralBorrowRawWildcardWindowPrefix
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver GeneralBorrowRawWildcardWindowInitial
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

structure Packet (s : Initial) (n : UInt64) where
  entry : GeneralBorrowRawWildcardWindowInitialize.Packet s n
  result : CompilerFrameContext.ActualFrame
  trace : SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits
    (Storage.withCurrent #[] (caller s n) (machine s entry.output entry.slotAllocation))
    (Storage.withCurrent #[] result (RootZeroCompleteState.tick s.options s.remaining s.span (machine s entry.output entry.slotAllocation)))
  shape : GenericFunctionEntryPrefix.Shape (caller s n) result n
  ready : GeneralBorrowRawWildcardFunctionToShared.Ready result (adjusted s) n
    ((({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag).addProtector s.slotId
      (GeneralBorrowRawWildcardWindowFunctionState.next s.tracker s.fresh).global.nextPointerTag)
  flags : GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.before
    (RootZeroCompleteState.tick s.options s.remaining s.span (machine s entry.output entry.slotAllocation))
  input : GeneralBorrowFreshRootScopedShared.Input entry.output.child.tree (global s).global
  parentTag : input.parentTag = s.tracker.global.nextPointerTag
  parent : input.parent = entry.child
  selected : input.selected = entry.child
  maximum : input.maximum = s.tracker.global.nextPointerTag
  inputOffset : input.offset = offset s
  inputLen : input.len = s.len
  buffer : (RootZeroCompleteState.tick s.options s.remaining s.span (machine s entry.output entry.slotAllocation)).memory.live.find? (fun row => row.1 == s.id) =
    some (s.id,{s.entry with allocation := s.entry.allocation.setExtra entry.output.child.tree})
  tracked : (RootZeroCompleteState.tick s.options s.remaining s.span (machine s entry.output entry.slotAllocation)).borrowTracker = some (global s)

/-- The same count-independent wildcard Initial starts a genuine call and
executes nonzero pure MIR to PC2:11. The next shared input is formed internally;
its creation, resulting heap and any future operation success are not premises. -/
theorem executes (s : Initial) (n : UInt64) (countPositive : (0 : UInt64) < n) : Nonempty (Packet s n) := by
  obtain ⟨output,run,allocation,result,call,trace,shape,ready,properties,currentRuntime,stored,tracked,child,lookup,owner,activity,
    input,parentTag,parent,selected,maximum,inputOffset,inputLen⟩ :=
    GeneralBorrowFreshRootScopedWildcardHitBackendInput.enters_shared_boundary
      s.options s.limits s.remaining s.span s.ctx s.debugOff s.cmp s.dynamicFuel s.validityFuel s.fuelEq s.validationEq s.id
      s.tracker s.address s.base s.len n s.nonzero s.entry s.positive s.signedFits s.bounds s.before s.ghost
      s.shallow s.cachedAddress s.present s.enabled s.fresh s.geometry s.addressMode s.exposedAlloc s.runtime s.capability s.distinct (by have h:=s.nodeHeadroom;omega)
      (by have h:=s.nodeHeadroom;omega) s.race s.metadata s.notConstructed s.retagCtx s.place s.layout s.slotId s.slotEntry s.slotBase s.slotRoot s.slotPointer
      s.aligned s.slotCached s.slotTree s.slotSize s.slotPresent s.separate s.slotFresh s.slotDistinct s.slotParentDistinct s.slotFree s.mutable s.storage
      s.maskLength s.provenance s.noBackend s.extras s.thread s.active s.noCache s.source s.mode countPositive s.unchecked s.noGc
      s.fixed s.nodeHeadroom s.tagHeadroom
  obtain ⟨entry,outputEq,allocationEq⟩ := GeneralBorrowRawWildcardWindowInitialize.described s n output run allocation call properties
  subst output
  subst allocation
  have same : child = entry.child := Option.some.inj (lookup.symm.trans entry.lookup)
  rw [same] at parent selected
  exact ⟨{
    entry := entry
    result := result
    trace := trace
    shape := shape
    ready := ready
    flags := GeneralBorrowRawWildcardWindowRuntime.tick_facts s entry.output entry.slotAllocation
    input := input
    parentTag := parentTag
    parent := parent
    selected := selected
    maximum := maximum
    inputOffset := inputOffset
    inputLen := inputLen
    buffer := stored
    tracked := tracked
  }⟩
end
end DuplicatePrefix.GeneralBorrowRawWildcardWindowPrefix
