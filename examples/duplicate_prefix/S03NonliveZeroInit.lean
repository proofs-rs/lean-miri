import duplicate_prefix.S03IntegerZeroInitTail
import duplicate_prefix.S03NonliveEmptyEntry
import duplicate_prefix.S03NonliveZeroState
import duplicate_prefix.ConcreteEmptyRootArgumentProperties

namespace DuplicatePrefix.S03NonliveZeroInit
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def tree {before : Before} {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (first : input.tracker.global.nextPointerTag.value < 18446744073709551615) (tag : BorTag) :=
  GeneralBorrowRawFnEntryArgument.finalTree input.entry.allocation.extra
    (⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩ : MachineHooks.BorrowState) tag input.offset 1

def global {before : Before} {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (first : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (second : (⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩ : MachineHooks.BorrowState).global.nextPointerTag.value < 18446744073709551615) :=
  TypedBorrowSteps.registeredGlobal
    (ReferenceBorrowDriver.allocatedTracker (⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩ : MachineHooks.BorrowState) second)
    (⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩ : MachineHooks.BorrowState).global.nextPointerTag

def written {before : Before} {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (first : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (second : (⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩ : MachineHooks.BorrowState).global.nextPointerTag.value < 18446744073709551615)
    (tag : BorTag) :=
  ((tree input first tag).performBorrowAccessRange
    (.concrete (⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩ : MachineHooks.BorrowState).global.nextPointerTag)
    (Size.ofBytes input.offset) (Size.ofBytes 1) .Write (global input first second).protectedTags .VisitChildrenOfAccessed).tree

def frame {before : Before} {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place) (race : before.dataRace = none)
    (argumentId : AllocId) (base offset count : UInt64) (first : input.tracker.global.nextPointerTag.value < 18446744073709551615) :=
  let adjusted := (RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base
    (Pointer.new (.concrete argumentId input.tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
  let args := RootArgumentsTwo.result (ConcreteEmptyRootArguments.firstDone
    (RawRootInvocation.root before place race) adjusted {} argumentId input.tracker.global.nextPointerTag) count
  CallEntryFacts.doneRootFrame {TypedBorrowSteps.registeredFrame
    {args.frame with location := .unwinding ⟨601⟩} (({} : FrameState).addProtector argumentId input.tracker.global.nextPointerTag) input.id
    (⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩ : MachineHooks.BorrowState).global.nextPointerTag
      with location := .unwinding ⟨559⟩}

def installed {before : Before} {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global) (race : before.dataRace = none)
    (argumentId : AllocId) (base offset count : UInt64) (first : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (second : (⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩ : MachineHooks.BorrowState).global.nextPointerTag.value < 18446744073709551615)
    (tag : BorTag) (updated : Allocation Provenance BorrowTree) : RootState :=
  let adjusted := (RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base
    (Pointer.new (.concrete argumentId input.tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
  let args := RootArgumentsTwo.result (ConcreteEmptyRootArguments.firstDone
    (RawRootInvocation.root before place race) adjusted {} argumentId input.tracker.global.nextPointerTag) count
  Storage.withCurrent #[] (frame input race argumentId base offset count first)
    (S04ProtectUninit.finished (S03NonliveZeroState.argumentsMachine before input.tracker first) place
      (S03NonliveZeroState.input input first argumentId runtime) #[] {args.frame with location := .unwinding ⟨601⟩} (({} : FrameState).addProtector argumentId input.tracker.global.nextPointerTag)
      second (tree input first tag) updated).machine

/-- Exact supported nonlive concrete empty initStackFrame for arbitrary count
and a general concrete return destination. The argument Strong protector is
retained, return protection/uninit is derived from current runtime data, and
no data tree is required for the nonlive argument. -/
theorem enters
    {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (limits : ExecutionMachine.Limits) (before : Before)
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (headroom : input.entry.allocation.extra.nodes.size+1 < 65536)
    (first : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (second : (⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩ : MachineHooks.BorrowState).global.nextPointerTag.value < 18446744073709551615)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag)
    (argumentId : AllocId) (parentTag : BorTag) (base offset count : UInt64) (nonzero : base+offset ≠ 0)
    (cached : before.user.addresses.baseAddr.find? (fun row => row.allocId == argumentId) = some ⟨argumentId,base⟩)
    (metadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory argumentId (some parentTag))
    (absent : before.memory.live.find? (fun row => row.1 == argumentId) = none)
    (dynamicFuel validityFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (validityEq : options.limits.validation = validityFuel+1)
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,#[]⟩))
    (thread : Miri.Concurrency.ThreadRecord) (active : before.threads.activeThread? = some thread)
    (noCache : thread.topUserRelevantFrame = none) :
    ∃ updated,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete argumentId parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (installed input runtime model.noDataRace argumentId base offset count first second tag updated) ∧
      updated.extra = written input first second tag ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut ∧
      InitMaskCopy.WellFormed updated.initializationMask ∧
      updated.initializationMask.len = input.entry.allocation.initializationMask.len ∧
      (∀ row ∈ updated.provenanceMap.ptrs, row.1.bytes.toNat+8≤updated.len) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts (written input first second tag) (global input first second) ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder (written input first second tag) ∧
      ∃ child, (written input first second tag).indexOfTag
          (⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩ : MachineHooks.BorrowState).global.nextPointerTag = some child ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive (written input first second tag) (global input first second).protectedTags
          (some child) input.selectedRoot input.maximum input.offset 1) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin (written input first second tag) child .Write input.offset (input.offset+1) := by
  let raw := RawRootInvocation.root before place model.noDataRace
  let rawMachine := RawRootInvocation.machine #[] before
  let adjusted := (RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base
    (Pointer.new (.concrete argumentId input.tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
  let args := RootArgumentsTwo.result
    (ConcreteEmptyRootArguments.firstDone raw adjusted {} argumentId input.tracker.global.nextPointerTag) count
  let current := S03NonliveZeroState.argumentsMachine before input.tracker first
  let currentInput := S03NonliveZeroState.input input first argumentId runtime
  have slot (i : Fin 25) : (raw.frame.locals[i.val]'(raw.valid i)) = ⟨.dead,none⟩ := by
    have rows := congrArg (fun rows : Array (LocalState Provenance LocalLayout) => rows[i.val]?)
      (RawRootInvocation.locals before place model.noDataRace)
    have row : raw.frame.locals[i.val]? = some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
      simpa only [Array.getElem?_replicate,i.isLt,↓reduceIte] using rows
    exact Option.some.inj ((Array.getElem?_eq_getElem (raw.valid i)).symm.trans row)
  let owned : FrameState := ({} : FrameState).addProtector argumentId input.tracker.global.nextPointerTag
  have frameBorrow : args.frame.extra.borrowTracker = some owned := by
    rfl
  have dead (i : Fin 25) (ne1 : i.val ≠ 1) (ne2 : i.val ≠ 2) :
      (args.frame.locals[i.val]'(args.valid i)).value = .dead := by
    rw [ConcreteEmptyRootArgumentProperties.untouched raw adjusted {} argumentId input.tracker.global.nextPointerTag count i ne1 ne2,slot i]
  obtain ⟨updated,tail,properties⟩ := S03IntegerZeroInitTail.run limits current
    (S03NonliveZeroState.model input model first) place currentInput (S03NonliveZeroState.runtime input first argumentId runtime)
    distinct order headroom second tag concrete #[] args.frame owned frameBorrow #[] extras (by simp)
    args.body args.size (dead ⟨0,by decide⟩ (by decide) (by decide))
    (dead ⟨6,by decide⟩ (by decide) (by decide)) (dead ⟨13,by decide⟩ (by decide) (by decide))
    (dead ⟨14,by decide⟩ (by decide) (by decide)) args.noClocks args.identity args.callee
  refine ⟨updated,?_,properties⟩
  have init := S03NonliveEmptyEntry.after_tail limits before model place input.tracker input.enabled first
    argumentId parentTag base offset count nonzero cached metadata absent dynamicFuel validityFuel dynamicEq validityEq
    notConstructed thread active noCache
  apply init
  simpa only [installed,frame,tree,args,raw,adjusted,currentInput,S03NonliveZeroState.input,owned,current,
    S03NonliveZeroState.argumentsMachine,CanonicalConfigFacts.actual_access_runtime] using tail

end
end DuplicatePrefix.S03NonliveZeroInit
