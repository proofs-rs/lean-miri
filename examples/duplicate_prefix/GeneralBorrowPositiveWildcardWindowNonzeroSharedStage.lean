import duplicate_prefix.GeneralBorrowPositiveWildcardWindowNonzeroInput
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowSharedCallPrefixBase
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowNonzeroSharedStage
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.DataStructures
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- The common original caller contract forms the real positive shared
expression prefix, retaining its exact physical frame and raw source resources. -/
theorem enters (s : GeneralBorrowPositiveWildcardWindowNonzeroInput.Initial) :
    let cfg := PreparedContracts.actualConfig s.options () (s.remaining+1) s.span
    let sharedValue := (RetagReferencePlace.sliceValue (ActualReferenceContext.config s.options s.remaining s.span).access.runtime.base
      (Pointer.new (.concrete s.id (GeneralBorrowPositiveWildcardWindowFunctionState.held s.tracker s.fresh s.slotFresh).global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len SharedReferenceMetadata.sharedLayout).imm
    ∃ installed beforeShared sharedFrame sharedMachine slotAllocation, ∃ input : GeneralBorrowFreshMetadataChildShared.Input,
      let held := GeneralBorrowPositiveWildcardWindowFunctionState.held s.tracker s.fresh s.slotFresh
      let current := RootZeroCompleteState.tick s.options s.remaining s.span
        (GeneralBorrowPositiveWildcardWindowFunctionState.enteredMachine (RawRootInvocation.machine #[] s.before) s.tracker s.fresh s.id s.entry s.offset s.len s.slotFresh s.slotId s.slotEntry s.slotRoot slotAllocation)
      let buffer := {s.entry with allocation := s.entry.allocation.setExtra (GeneralBorrowPositiveWildcardWindowArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.offset s.len)}
      let adjusted := (RetagReferencePlace.sliceValue (ActualReferenceContext.config s.options s.remaining s.span).access.runtime.base
        (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm
      let entryFrame := PositiveRootInstalledFrame.installed (RawRootInvocation.root s.before s.place s.race) adjusted s.count {} s.id s.tracker.global.nextPointerTag
        s.slotId (GeneralBorrowPositiveWildcardWindowFunctionState.next s.tracker s.fresh).global.nextPointerTag
      Call.initStackFrame (ExecutionMachine.callHooks cfg s.limits) () RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config s.options s.remaining s.span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
          .Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace cfg s.limits installed (Storage.withCurrent #[] sharedFrame sharedMachine) ∧
      GeneralBorrowForestSharedPreLenFrame.Facts beforeShared sharedFrame s.count sharedValue ∧
      GenericFunctionEntryPrefix.Shape entryFrame beforeShared s.count ∧
      GeneralBorrowPositiveWildcardWindowFunctionToShared.Ready beforeShared adjusted s.count
        ((({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag).addProtector s.slotId
          (GeneralBorrowPositiveWildcardWindowFunctionState.next s.tracker s.fresh).global.nextPointerTag) ∧
      (∃ valid : 12 < beforeShared.locals.size, sharedFrame = GeneralBorrowForestSharedPreLenFrame.after beforeShared valid sharedValue) ∧
      input.tree = buffer.allocation.extra ∧ input.parentTag = s.tracker.global.nextPointerTag ∧
      input.newTag = held.global.nextPointerTag ∧ input.parent = ⟨UInt32.ofNat s.entry.allocation.extra.tagMapping.mapping.size⟩ ∧
      input.isProtected = false ∧ input.offset = s.offset ∧ input.len = s.len ∧
      (∃ raw : GeneralBorrowExposedScopedWritableSharedConstructor.Resources input held.global.protectedTags
        ⟨UInt32.ofNat s.entry.allocation.extra.tagMapping.mapping.size⟩ s.head
        (s.extraRoots++[⟨UInt32.ofNat s.entry.allocation.extra.tagMapping.mapping.size⟩]) (fun _=>true),
        raw.component.support = (fun position => position = (⟨UInt32.ofNat s.entry.allocation.extra.tagMapping.mapping.size⟩ : UniIndex).toNat)) ∧
      sharedMachine = {ReferenceBorrowDriver.allocatedMachine current held s.sharedFresh with
        memory := RetagEntry.updatedMemory current.memory s.id buffer (GeneralBorrowForestMixedShared.child buffer.allocation.extra held.global.protectedTags
          s.tracker.global.nextPointerTag held.global.nextPointerTag false s.offset s.len .VisitChildrenOfAccessed).tree} ∧
      slotAllocation.extra = PhysicalMachineWrite.slotTree s.slotRoot (GeneralBorrowPositiveWildcardWindowFunctionState.next s.tracker s.fresh).global.nextPointerTag 1 true ∧
      slotAllocation.byteSize = Size.ofBytes 1 ∧ slotAllocation.len = 1 ∧
      slotAllocation.initializationMask = InitMask.new (Size.ofBytes 1) false ∧ slotAllocation.provenanceMap = ProvenanceMap.new ∧
      AllocationCopy.snapshot slotAllocation = AllocationCopy.snapshot s.slotEntry.allocation ∧ slotAllocation.mutability = .Mut := by
  exact GeneralBorrowPositiveWildcardWindowSharedCallPrefixBase.enters_pre_len_base s.toBase s.countPositive
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowNonzeroSharedStage
