import duplicate_prefix.DuplicatePrefixArgumentCallResult
import duplicate_prefix.SuccessfulTraceTerminal
import duplicate_prefix.S02SeparateDestinationStateJoin
import duplicate_prefix.S03FinalReturnInputBounds
import duplicate_prefix.S02SameDestinationAcceptedCopyPhysical

namespace DuplicatePrefix.S02SameDestinationAcceptedResultJoin
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Restrict initialization to the actual accepted copy source interval. -/
theorem initialized_subrange (mask : InitMask) (start finish shortFinish : Size)
    (initialized : InitMaskCopy.InitializedOn mask start finish)
    (upper : shortFinish.bytes.toNat ≤ finish.bytes.toNat) :
    InitMaskCopy.InitializedOn mask start shortFinish := by
  unfold InitMaskCopy.InitializedOn at initialized ⊢
  cases blocksEq : mask.blocks with
  | Lazy state => simpa only [blocksEq] using initialized
  | Materialized blocks =>
    simp only [blocksEq] at initialized
    intro block valid bit small lower upperBit
    exact initialized block valid bit small lower (Nat.lt_of_lt_of_le upperBit upper)

/-- Reconstruct the current physical return destination after the real copy.
Byte contents may change; mask and provenance bounds refer to the exact current
allocation witness. Borrow authorization is supplied separately to Return. -/
def destination
    {place : MPlaceTy Provenance}
    {machine post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    (original : S03FinalReturnInputBounds.Destination machine place)
    (result : Allocation Provenance BorrowTree)
    (live : post.memory.live.find? (fun row => row.1 == original.id) =
      some (original.id,⟨original.entry.kind,result⟩))
    (addresses : post.user.addresses = machine.user.addresses)
    (size : result.byteSize = original.entry.allocation.byteSize)
    (length : result.len = original.entry.allocation.len)
    (physical : S02SameDestinationAcceptedCopyPhysical.Physical result)
    (capacity : result.extra.locations.size = original.entry.allocation.extra.locations.size)
    (tagged : result.extra.indexOfTag original.tag = some original.parent) :
    S03FinalReturnInputBounds.Destination post place := {
  pointer := original.pointer, physicalPointer := original.physicalPointer,
  layout := original.layout, aligned := original.aligned,
  id := original.id, entry := ⟨original.entry.kind,result⟩,
  base := original.base, offset := original.offset, capacity := original.capacity,
  live := live, cachedBase := by rw [addresses];exact original.cachedBase,
  pointerAddress := original.pointerAddress, nonnull := original.nonnull,
  addressFits := original.addressFits, bounds := original.bounds,
  size := size.trans original.size, bytes := length.trans original.bytes,
  mutable := physical.mutable, maskValid := physical.maskValid,
  maskLength := physical.maskLength.trans (size.trans original.size),
  pointerBounds := physical.pointerBounds,
  borrowSize := by change result.extra.locations.size.bytes = original.capacity;rw [capacity];exact original.borrowSize,
  tag := original.tag, parent := original.parent,
  concrete := original.concrete, tagged := tagged }

/-- Close the original call postcondition from its actual installed frame,
complete successful trace, empty final stack, and normal terminal step.
This is a trace-assembly component, not a caller contract or a standalone
accepted-input theorem. -/
theorem finish
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (before : Before)
    (place : MPlaceTy Provenance) (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (entry : CompilerFrameContext.ActualFrame)
    (initial : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (finished : RootState)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
        (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
        .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
      ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry initial))
    (trace : SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] entry initial) finished)
    (empty : finished.stack.frames = #[])
    (terminal : ExecutionMachine.step (config options (remaining+1) span) limits () finished =
      (finished,.ok false)) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len count place := by
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
    ⟨config options (remaining+1) span,limits,fun _ _ => True⟩
  have entered : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] entry initial) := by
    simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent]
  have exited : CallSafety.pastCallBoundary 1 finished := by
    simp [CallSafety.pastCallBoundary,CallSafety.frameDepth,empty]
  exact ⟨Storage.withCurrent #[] entry initial,finished,actual,trace,terminal,empty,
    SuccessfulTrace.no_errors safety 1 _ finished entered trace exited,
    SuccessfulTrace.no_ub safety 1 _ finished entered trace exited,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.S02SameDestinationAcceptedResultJoin

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.S02SameDestinationAcceptedResultJoin.finish,
      ``DuplicatePrefix.S02SameDestinationAcceptedResultJoin.destination,
      ``DuplicatePrefix.S02SameDestinationAcceptedResultJoin.initialized_subrange] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved same accepted result join dependency {dependency}"
