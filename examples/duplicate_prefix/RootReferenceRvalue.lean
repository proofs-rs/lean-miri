import duplicate_prefix.RootReferencePlace
import duplicate_prefix.RootReferenceWrite
import duplicate_prefix.SliceLenRawRvalue
namespace DuplicatePrefix.RootReferenceRvalue
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts RootReferenceInfo
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def borrowKind (shared : Bool) : BorrowKind := if shared then .Shared else .Mut .TwoPhaseBorrow

def enter (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (shared : Bool) :=
  {machine with borrowTracker := some {tracker with retagMode := mode shared}}

theorem of_write
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (shared : Bool) (region : Region) (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64)
    (source dest : MIR.Place) (destValue : RuntimePlace Provenance)
    (state0 : RootState) (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker newTracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (shallow : machine.user.payload.validation = .Shallow)
    (destLayout : destValue.layout = layout shared)
    (destination : (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).evalPlace
      () dest true state0 = .ok destValue (Storage.withCurrent frames frame machine))
    (sourcePlace : (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).evalPlace
      () source true (Storage.withCurrent frames frame machine) =
      .ok ⟨.memory (SliceLenRawRvalue.carrierMemory carrier len),ProjectionMetadataFacts.sliceLayout⟩ (Storage.withCurrent frames frame machine))
    (afterFrame : CompilerFrameContext.ActualFrame)
    (afterMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (trackedAfter : afterMachine.borrowTracker = some newTracker)
    (write : (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).writeImmediate
      () (PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)
      destValue (Storage.withCurrent frames frame (enter machine tracker shared)) =
      .ok () (Storage.withCurrent frames afterFrame afterMachine)) :
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits) ()
      (.Ref region (borrowKind shared) source) dest state0 =
      .ok () (Storage.withCurrent frames afterFrame
        {afterMachine with borrowTracker := some {newTracker with retagMode := tracker.retagMode}}) := by
  let cfg := PreparedContracts.actualConfig options () remaining span
  let hooks := ExecutionMachine.rvalueHooks cfg limits
  let state := Storage.withCurrent frames frame machine
  let entered := Storage.withCurrent frames frame (enter machine tracker shared)
  let value : RvalueImmTy Provenance := ⟨PtrMetadataComplete.rawImmediate carrier cfg.access.runtime.base len,layout shared⟩
  have allocated : hooks.forceAllocation () ⟨.memory (SliceLenRawRvalue.carrierMemory carrier len),ProjectionMetadataFacts.sliceLayout⟩ state =
      .ok (SliceLenRawRvalue.carrierMemory carrier len) state := rfl
  have reference : hooks.toRef () (SliceLenRawRvalue.carrierMemory carrier len) state = .ok value.imm state := by
    change (ExecutionMachine.rvalueHooks cfg limits).toRef () (SliceLenRawRvalue.carrierMemory carrier len) state = _
    unfold ExecutionMachine.rvalueHooks
    dsimp only
    unfold_internal ".ExecutionMachine.lift"
    rw [show (ExecutionMachine.withValidation cfg limits).access = cfg.access from rfl]
    rw [SliceLenRawRvalue.carrier_to_ref carrier cfg.access.runtime.base len (CanonicalConfigFacts.actual_target_width options () remaining span)]
    rfl
  have enforced : hooks.enforceValidity () (layout shared) entered = .ok true entered := by
    change cfg.compiler.enforceValidity () (layout shared) entered = _
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).compilerEnforce]
    simp [ValidityMachine.enforceValidity,entered,enter,Storage.withCurrent,shallow,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  have kindMode : (if borrowKind shared == BorrowKind.Mut .TwoPhaseBorrow then RetagPolicy.RetagMode.TwoPhase else .Default) = mode shared := by
    cases shared <;> decide
  change evalRvalueIntoPlace hooks () (.Ref region (borrowKind shared) source) dest state0 = _
  unfold evalRvalueIntoPlace
  simp only [bind,EStateM.bind]
  rw [destination]
  simp only
  have placeLayout : hooks.placeLayout destValue = layout shared := destLayout
  simp only [placeLayout]
  have sourcePlace' : hooks.evalPlace () source true state =
      .ok ⟨.memory (SliceLenRawRvalue.carrierMemory carrier len),ProjectionMetadataFacts.sliceLayout⟩ state := sourcePlace
  dsimp only [state] at sourcePlace' allocated reference
  simp only [sourcePlace',allocated,reference,kindMode]
  change MachineHooks.withRetagMode (mode shared) _ (Storage.withCurrent frames frame machine) = _
  unfold MachineHooks.withRetagMode
  simp only [Storage.withCurrent,enabled]
  simp only [entered,enter,Storage.withCurrent] at enforced
  simp only [bind,EStateM.bind,enforced,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  simp only [enter,Storage.withCurrent] at write
  rw [write]
  simp [Storage.withCurrent,trackedAfter]

#print axioms of_write
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``of_write) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved axiom {dependency}"
end
end DuplicatePrefix.RootReferenceRvalue
