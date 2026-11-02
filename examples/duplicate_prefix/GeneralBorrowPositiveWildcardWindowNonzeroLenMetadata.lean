import duplicate_prefix.GeneralBorrowPositiveWildcardWindowNonzeroMachinePrefixMetadata
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowNonzeroLenMetadata
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend PtrMetadataExecution PtrMetadataReturn
open GeneralBorrowProjection GeneralBorrowPositiveWildcardWindowNonzeroInput
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Original wildcard initStackFrame through the real positive shared
expression, len helper call/body/return/release/pop/endCall and ROOT PC3:0.
All intermediate resources, Write/Read readiness and successful steps are
internally derived from the original caller contract. -/
theorem invoke (s : Initial) :
    ∃ (updated : Allocation Provenance BorrowTree) (input : GeneralBorrowExposedScopedWindowWritableLenCallInput.Input), ∃ installed,
      GeneralBorrowPositiveWildcardWindowNonzeroMachinePrefixMetadata.Origin s updated input ∧
      Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
          .Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩=.ok () installed ∧
    let childTree := GeneralBorrowExposedScopedSharedArgumentCopy.finalTree input.entry.allocation.extra input.tracker input.exprTag input.offset input.len
    let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker input.tracker input.fresh) input.tracker.global.nextPointerTag
    let borrowFrame := ({} : FrameState).addProtector input.id input.tracker.global.nextPointerTag
    ∃ (root : CompilerFrameContext.ActualFrame) (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (released : BorrowTree),
      SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits
        installed (Storage.withCurrent #[] root post) ∧
      root={writeFrame (cachedCaller input.caller input.valid) 11 (.scalar (.fromScalarInt (.ofUInt64 input.len)))
        (by simpa [cachedCaller,LocalPlaces.cachePlaceLayout] using input.valid) with location:=.mir ⟨3,0⟩} ∧
      post.memory=RetagEntry.updatedMemory input.beforeMachine.memory input.id input.entry released ∧
      post.borrowTracker=some {held with global:=held.global.endCall borrowFrame} ∧
      childTree.releaseProtector input.tracker.global.nextPointerTag held.global.protectedTags=⟨released,.Released⟩ ∧
      GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (GeneralBorrowExposedScopedWritableReadData.Data released location held.global.protectedTags
        (GeneralBorrowFreshMetadataChildShared.index input.input) input.selected input.head input.tail
        (fun position => input.raw.component.support position ∨ position=(GeneralBorrowFreshMetadataChildShared.index input.input).toNat)
        (GeneralBorrowFreshMixedChild.extend input.writable (GeneralBorrowFreshMetadataChildShared.index input.input).toNat)))
        input.offset (input.offset+input.len) released.locations ∧
      released.locations.WellFormed ∧ released.locations.size=input.entry.allocation.extra.locations.size ∧
      GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts input.options input.remaining input.span input.beforeMachine post ∧
      (input.frames=#[] → GenericSharedLenAccepted.RuntimeFacts input.options input.remaining input.span input.beforeMachine post) ∧
      post.memory.live.find? (fun row=>row.1==input.id)=some (input.id,{input.entry with allocation:=input.entry.allocation.setExtra released}) ∧
      GeneralBorrowGcAllocator.NodeTags released ∧
      ∃ writeContext : GeneralBorrowExposedKnownRootRangeData.Context released input.first.parent input.selected input.head input.tail,
        GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedKnownRootRangeData.Data released location
          (held.global.endCall borrowFrame).protectedTags input.first.parent input.selected input.head input.tail .Write)) input.offset (input.offset+input.len) released.locations ∧
        GeneralRangeMapOrigins.OwnedOn (fun location=>GeneralBorrowExposureCardinality.LocationCoherent released location
          (held.global.endCall borrowFrame).protectedTags) input.offset (input.offset+input.len) released.locations ∧
        GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedKnownRootRangeData.Data released location
          (held.global.endCall borrowFrame).protectedTags input.first.parent input.selected input.head input.tail .Read)) input.offset (input.offset+input.len) released.locations ∧
        GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedScopedWritableReadData.Data released location
          (held.global.endCall borrowFrame).protectedTags input.first.parent input.selected input.head input.tail
          (fun position=>input.raw.component.support position ∨position=(GeneralBorrowFreshMetadataChildShared.index input.input).toNat)
          (fun _=>true))) input.offset (input.offset+input.len) released.locations := by
  obtain ⟨updated,input,installed,call,prefixTrace,origin⟩ := GeneralBorrowPositiveWildcardWindowNonzeroMachinePrefixMetadata.forms s
  obtain ⟨root,post,released,lenTrace,rest⟩ := GeneralBorrowExposedScopedWindowWritableLenCallInput.executes input
  have actualTrace : SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits installed
      (Storage.withCurrent #[] root post) := by
    rw [origin.options,origin.limits,origin.remaining,origin.span,origin.frames] at lenTrace
    exact SuccessfulTrace.append prefixTrace lenTrace
  exact ⟨updated,input,installed,origin,call,root,post,released,actualTrace,rest⟩

/-- Runtime metadata from the actual helper result composes with the physical
prefix's original-caller metadata without any new external runtime premise. -/
theorem runtime_trans (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before middle after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (first : GenericSharedLenAccepted.RuntimeFacts options remaining span before middle)
    (second : GenericSharedLenAccepted.RuntimeFacts options remaining span middle after) :
    GenericSharedLenAccepted.RuntimeFacts options remaining span before after :=
  ⟨second.ghost,second.shallow,second.race,second.addresses.trans first.addresses,second.types.trans first.types,
    second.extras.trans first.extras,second.backend,second.unchecked,second.noGc,second.fixed,second.active⟩
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowNonzeroLenMetadata
