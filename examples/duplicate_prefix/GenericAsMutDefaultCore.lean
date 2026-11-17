import duplicate_prefix.GenericAsMutCallToReturn
import duplicate_prefix.GenericRootDefaultBorrow
namespace DuplicatePrefix.GenericAsMutDefaultCore
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open GeneralRangeMapOrigins GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- The pre-call graph data also construct the actual unprotected mutable
expression; its operation outcome is not included in the initial contract. -/
def first (s : GenericAsMutInvocationCore.Input) :
    GeneralBorrowFreshDefaultSequence.Data s.entry.allocation.extra s.tracker.global.nextPointerTag s.data.parent s.offset s.len := by
  refine {
    parentTag := s.parentTag, root := s.data.root, parentNode := s.data.node, depth := s.data.depth
    children := s.data.children, parentPresent := s.data.parentPresent, roots := s.data.roots, covered := s.data.covered
    parentTagPresent := s.data.tagPresent, tagFresh := s.data.tagFresh, nodeFits := s.data.nodeFits, slot := s.data.slot
    nonzero := ?_, well := s.data.well, bounds := ?_, clean := ?_ }
  · intro zero
    have bad := s.positive
    rw [zero] at bad
    exact (show ¬ ((0 : UInt64) < 0) from by decide) bad
  · rw [s.capacity]
    exact s.bounds
  · have same : GeneralBorrowFreshDefaultStages.slot_index s.data.slot =
        GeneralBorrowFreshMutableStages.slot_index s.data.slot := by cases s.data.slot <;> rfl
    rw [same]
    exact s.clean

set_option autoImplicit false in
/-- Source caller before the mutable-expression statement. The auxiliary
cached-15 frame is a static view, while the actual frame still has no layout. -/
structure Input where
  data : GenericAsMutInvocation.Input
  caller : CompilerFrameContext.ActualFrame
  valid15 : (15 : MIR.LocalId) < caller.locals.size
  cached : data.start.caller = AsMutUncachedCall.cachedCaller caller valid15
  live15 : caller.locals[15].value = .live (.immediate .uninit)
  uncached15 : caller.locals[15].layout = none
  preciseOff : data.start.options.retag.preciseInteriorMut = false
  implicitOff : data.start.options.retag.implicitWrites = false
  location : caller.location = .mir ⟨6,7⟩
  valid1 : (1 : MIR.LocalId) < caller.locals.size
  value1 : caller.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
    (PreparedContracts.actualConfig data.start.options () (data.start.remaining+1) data.start.span).access.runtime.base
    (Pointer.new (.concrete data.start.id data.start.parentTag) (Size.ofBytes (data.start.base+data.start.offset)))
    data.start.len ActualReferenceMetadata.reference).imm)
  cached1 : caller.locals[1].layout = some ActualReferenceMetadata.reference
  valid16 : (16 : MIR.LocalId) < caller.locals.size
  live16 : caller.locals[16].value = .live (.immediate .uninit)
  uncached16 : caller.locals[16].layout = none

def value (s : GenericAsMutInvocationCore.Input) :=
  (RetagReferencePlace.sliceValue (ActualReferenceContext.config s.options s.remaining s.span).access.runtime.base
    (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len
    (RootReferenceInfo.layout false)).imm

def frame (input : Input) :=
  CopyHelperSteps.advance (ActualLocalCopy.written input.caller 16 (RootReferenceInfo.layout false) input.valid16
    (value input.data.start)) ⟨6,7⟩

def machine (s : GenericAsMutInvocationCore.Input) :=
  {ReferenceBorrowDriver.allocatedMachine s.machine s.tracker s.fresh with
    memory := RetagEntry.updatedMemory s.machine.memory s.id s.entry
      (GeneralBorrowFreshDefaultSequence.child (first s) s.tracker.global.protectedTags).tree}

/-- Execute the actual source mutable-expression statement at PC6:7. -/
theorem step (input : Input) :
    let s := input.data.start
    ExecutionMachine.step (PreparedContracts.actualConfig s.options () (s.remaining+1) s.span) s.limits ()
      (Storage.withCurrent #[] input.caller s.machine) =
      (Storage.withCurrent #[] (frame input) (machine s),.ok true) := by
  let s := input.data.start
  have sourceBody : input.caller.body = RootBody.reflected.body.body := by
    have same := s.body
    rw [input.cached] at same
    exact same
  have identity : input.caller.bodyIdentity = RootBody.reflected.body.identity := by
    have same := s.identity
    rw [input.cached] at same
    exact same
  have callee : input.caller.functionInstance = RootBody.reflected.functionInstance := by
    have same := s.callee
    rw [input.cached] at same
    exact same
  have clocks : input.caller.extra.dataRace = none := by
    have same := s.clocks
    rw [input.cached] at same
    exact same
  exact GenericRootDefaultBorrow.positive_statement s.options s.limits s.remaining s.span input.preciseOff input.implicitOff s.debug s.cmp
    s.dynamicFuel s.fuel s.dynamic s.validation s.base s.offset s.len s.id s.entry s.positive s.nonzero s.signedFits
    #[] input.caller s.machine sourceBody identity callee input.location s.tracker s.tracked s.mode s.fresh s.data.parent (first s)
    s.capacity s.data.owned input.valid1 input.valid16 input.value1 input.cached1 input.live16 input.uncached16 clocks
    s.ghost s.shallow s.cachedAddress s.present s.race s.metadata s.notConstructed
end
end DuplicatePrefix.GenericAsMutDefaultCore
