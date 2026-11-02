import duplicate_prefix.GeneralBorrowPositiveWildcardWindowAcceptedCallSource
import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableAcceptedGraphMetadata
import duplicate_prefix.GeneralBorrowScopedWritableCopyRootGuardBody
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowAcceptedCopyData
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GeneralBorrowExposedScopedWindowWritableAsMutCallReturn
open GeneralBorrowExposedScopedWindowWritableAsMutToCopy
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

private theorem maximum (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (config options remaining span).projection.maxSizeOfVal=Size.ofBytes 9223372036854775807 := by
  have fields:=CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨placeOptions,pointers,table,compilerEq,projectionEq,_⟩:=fields.placeConstruction
  have same : (config options remaining span).projection.maxSizeOfVal=(config options remaining span).projection.dynamic.maxSizeOfVal := by
    rw [projectionEq]
    rfl
  obtain ⟨sourceTable,bound,boundEq,dynamicEq⟩:=fields.projectionDynamic
  rw [same,dynamicEq]
  change bound=Size.ofBytes 9223372036854775807
  exact Except.ok.inj (boundEq.symm.trans (show CompilerExecutionBounds.maximum PreparedReflection.actual.compiler.runtime.target=
    .ok (Size.ofBytes 9223372036854775807) from rfl))

abbrev ended (call : Input) := (GeneralBorrowExposedScopedWindowWritableAsMutCallInput.held call.toInput).global.endCall
  (({} : FrameState).addProtector call.id call.tracker.global.nextPointerTag)
abbrev anchor (call : Input) := GeneralBorrowFreshMetadataChildMutable.index call.data.input

variable (s : GeneralBorrowPositiveWildcardWindowAcceptedInput.Initial)
  (sourceInitialized : InitMaskCopy.InitializedOn s.entry.allocation.initializationMask (Size.ofBytes s.offset) (Size.ofBytes (s.offset+s.count)))
  (updated : Allocation Provenance BorrowTree)
  (i : GeneralBorrowExposedScopedWindowWritableLenCallInput.Input) (stage : GeneralBorrowExposedScopedWindowWritableAcceptedAfterLen.Initial)
  (expression : GeneralBorrowExposedScopedWindowWritableAcceptedExpression.Input) (call : Input)
  (origin : GeneralBorrowPositiveWildcardWindowAcceptedAfterLen.Origin s updated i stage)
  (expressionOrigin : GeneralBorrowExposedScopedWindowWritableAcceptedAfterLen.Origin stage expression)
  (callOrigin : GeneralBorrowExposedScopedWindowWritableAcceptedToAsMut.Origin expression call.toInput)
  (countEq : call.count=s.count)
  (root : CompilerFrameContext.ActualFrame) (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
  (memoryEq : post.memory=RetagEntry.updatedMemory call.machine.memory call.id call.entry (released call.toInput))
  (trackedEq : post.borrowTracker=some {GeneralBorrowExposedScopedWindowWritableAsMutCallInput.held call.toInput with global:=ended call})
  (runtime : GenericSharedLenAccepted.RuntimeFacts call.options call.remaining call.span call.machine post)
  (context : GeneralBorrowExposedKnownRootRangeData.Context (released call.toInput) (anchor call) call.selected call.head call.tail)
  (owned : GeneralRangeMapOrigins.OwnedOn (fun location=>
    Nonempty (GeneralBorrowExposedScopedWritableReadData.Data (released call.toInput) location (ended call).protectedTags
      (anchor call) call.selected call.head call.tail
      (fun position=>call.data.resources.component.support position ∨ position=(anchor call).toNat) (fun _=>true)) ∧
    Nonempty (GeneralBorrowExposedKnownRootRangeData.Data (released call.toInput) location (ended call).protectedTags
      (anchor call) call.selected call.head call.tail .Write) ∧
    Nonempty (GeneralBorrowExposedScopedLeafWriteReadClosed.Data (released call.toInput) location (ended call).protectedTags
      (anchor call) call.selected call.head call.tail)) call.offset (call.offset+call.len) (released call.toInput).locations)
  (well : (released call.toInput).locations.WellFormed)
  (capacity : (released call.toInput).locations.size=call.entry.allocation.extra.locations.size)
  (copy : CopyRootEntry.Input call.options call.limits call.remaining call.span #[] root post (scalar call) (destinationScalar call) call.count)

include trackedEq in
theorem tracker_eq : copy.tracker={GeneralBorrowExposedScopedWindowWritableAsMutCallInput.held call.toInput with global:=ended call} :=
  Option.some.inj (copy.tracked.symm.trans trackedEq)

/-- All physical and borrow inputs for the real ROOT copy are formed from
original caller storage, actual helper output data and its real source graph.
The scalar pointer definitions retain the actual allocated helper tag. -/
def form : GeneralBorrowScopedWritableCopyRootGuardBody.CopyData call.options call.remaining call.span post copy.tracker
    (scalar call) (destinationScalar call) call.count := by
  let source:=GeneralBorrowPositiveWildcardWindowAcceptedCallSource.build s updated i stage expression call origin expressionOrigin callOrigin sourceInitialized
  have graph:=GeneralBorrowExposedScopedWindowWritableAcceptedGraphMetadata.metadata expression call.toInput callOrigin
  have copied:=PositiveRootCopyBounds.guarded call.len call.count call.offset call.entry.allocation.byteSize.bytes call.within call.bounds
  have same:=tracker_eq call root post trackedEq copy
  have borrow : GeneralBorrowScopedWritableCopyInput.Input (released call.toInput) copy.tracker.global.protectedTags call.tracker.global.nextPointerTag call.offset call.len call.count := {
    anchor:=anchor call,selected:=call.selected,head:=call.head,tail:=call.tail,context:=context,
    fits:=graph.2.2.2.1,covered:=graph.2.1,tagPresent:=graph.2.2.2.2.1,well:=well,
    bounds:=by rw [capacity,call.capacity];exact call.bounds,twice:=copied.2.1,
    support:=fun position=>call.data.resources.component.support position ∨ position=(anchor call).toNat,
    owned:=by
      rw [same]
      intro position valid positive start stop
      exact (owned position valid positive start stop).1 }
  exact {
    id:=call.id,tag:=call.tracker.global.nextPointerTag,base:=call.base,offset:=call.offset,sliceLen:=call.len,
    kind:=call.entry.kind,allocation:=call.entry.allocation.setExtra (released call.toInput),positive:=call.countPositive,
    sliceBounds:=call.bounds,copyBounds:=copied.2.1,storage:=source.storage,maskValid:=source.maskValid,maskLen:=source.maskLength,
    initialized:=by rw [countEq];exact source.initialized,
    valid:=source.provenance,storageFits:=source.storageFits,mutable:=source.mutable,
    extras:=by rw [runtime.extras];exact source.bufferExtras,
    live:=by rw [memoryEq];exact StackPopRelease.lookup_commit_same call.machine.memory call.id call.entry (released call.toInput),
    cached:=by rw [runtime.addresses];exact call.cachedAddress,
    borrow:=borrow,
    bounded:=by
      rw [maximum]
      apply UInt64.le_iff_toNat_le.mpr
      change call.count.toNat≤9223372036854775807
      have low:=copied.1
      omega,
    source:=rfl,
    destination:=by simp only [destinationScalar,UInt64.add_assoc] }

include trackedEq in
theorem mode : copy.tracker.retagMode=.Default := by
  rw [tracker_eq call root post trackedEq copy]
  exact call.mode

include sourceInitialized origin expressionOrigin callOrigin in
theorem fuel : copy.fuel=s.validityFuel := by
  have source:=GeneralBorrowPositiveWildcardWindowAcceptedCallSource.build s updated i stage expression call origin expressionOrigin callOrigin sourceInitialized
  have actual:=copy.validationFuel
  have optionsEqual:=congrArg (fun options : EvalConfigurationCore.Options=>options.limits.validation) source.options
  have configured:=s.validationEq
  omega

include sourceInitialized origin expressionOrigin callOrigin in
theorem statement_fuel (statementFuel : s.limits.validation=s.validityFuel+1) : call.limits.validation=copy.fuel+1 := by
  have source:=GeneralBorrowPositiveWildcardWindowAcceptedCallSource.build s updated i stage expression call origin expressionOrigin callOrigin sourceInitialized
  have actualLimits:=congrArg (fun limits : ExecutionMachine.Limits=>limits.validation) source.limits
  have actualFuel:=fuel s sourceInitialized updated i stage expression call origin expressionOrigin callOrigin root post copy
  omega

end
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowAcceptedCopyData
