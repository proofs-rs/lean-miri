import duplicate_prefix.S03IntegerZeroInitTail

namespace DuplicatePrefix.S03IntegerZeroInit
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
    (ReferenceBorrowDriver.allocatedTracker input.tracker first) tag input.offset 1

def global {before : Before} {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (first : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (second : (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag.value < 18446744073709551615) :=
  TypedBorrowSteps.registeredGlobal
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker input.tracker first) second)
    (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag

def written {before : Before} {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (first : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (second : (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag.value < 18446744073709551615)
    (tag : BorTag) :=
  ((tree input first tag).performBorrowAccessRange
    (.concrete (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag)
    (Size.ofBytes input.offset) (Size.ofBytes 1) .Write (global input first second).protectedTags .VisitChildrenOfAccessed).tree

def frame {before : Before} {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place) (race : before.dataRace = none)
    (address count : UInt64) (first : input.tracker.global.nextPointerTag.value < 18446744073709551615) :=
  let args := EmptyRootArguments.result (RawRootInvocation.root before place race) address count
  CallEntryFacts.doneRootFrame {TypedBorrowSteps.registeredFrame
    {args.frame with location := .unwinding ⟨601⟩} {} input.id
    (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag
      with location := .unwinding ⟨559⟩}

def installed {before : Before} {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place) (race : before.dataRace = none)
    (address count : UInt64) (first : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (second : (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag.value < 18446744073709551615)
    (tag : BorTag) (updated : Allocation Provenance BorrowTree) : RootState :=
  let args := EmptyRootArguments.result (RawRootInvocation.root before place race) address count
  Storage.withCurrent #[] (frame input race address count first)
    (S04ProtectUninit.finished (S03IntegerZeroState.argumentsMachine before input.tracker first) place
      (S03IntegerZeroState.input input first) #[] {args.frame with location := .unwinding ⟨601⟩} {}
      second (tree input first tag) updated).machine

/-- The original integer/NoProv empty argument initStackFrame for arbitrary count,
from original physical/borrow/configuration data. The real first argument
consumes a tag without installing a protector; return protection uses only
its residual local margin. No future Input or successful helper is assumed. -/
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
    (second : (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag.value < 18446744073709551615)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag)
    (address count : UInt64) (nonzero : address ≠ 0)
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
        #[.Copy (EmptyRootArguments.first address),.Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (installed input model.noDataRace address count first second tag updated) ∧
      updated.extra = written input first second tag ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut ∧
      InitMaskCopy.WellFormed updated.initializationMask ∧
      updated.initializationMask.len = input.entry.allocation.initializationMask.len ∧
      (∀ row ∈ updated.provenanceMap.ptrs, row.1.bytes.toNat+8≤updated.len) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts (written input first second tag) (global input first second) ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder (written input first second tag) ∧
      ∃ child, (written input first second tag).indexOfTag
          (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag = some child ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive (written input first second tag) (global input first second).protectedTags
          (some child) input.selectedRoot input.maximum input.offset 1) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin (written input first second tag) child .Write input.offset (input.offset+1) := by
  let raw := RawRootInvocation.root before place model.noDataRace
  let rawMachine := RawRootInvocation.machine #[] before
  let args := EmptyRootArguments.result raw address count
  let current := S03IntegerZeroState.argumentsMachine before input.tracker first
  let currentInput := S03IntegerZeroState.input input first
  have slot (i : Fin 25) : (raw.frame.locals[i.val]'(raw.valid i)) = ⟨.dead,none⟩ := by
    have rows := congrArg (fun rows : Array (LocalState Provenance LocalLayout) => rows[i.val]?)
      (RawRootInvocation.locals before place model.noDataRace)
    have row : raw.frame.locals[i.val]? = some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
      simpa only [Array.getElem?_replicate,i.isLt,↓reduceIte] using rows
    exact Option.some.inj ((Array.getElem?_eq_getElem (raw.valid i)).symm.trans row)
  have arguments := EmptyRootArgumentScope.arguments_in_scope options limits remaining span model.nullComparator
    model.preciseOff model.implicitOff model.debugOff dynamicFuel validityFuel dynamicEq validityEq #[] raw rawMachine address count nonzero
    (congrArg (fun row => row.value) (slot EmptyRootArguments.i1))
    (congrArg (fun row => row.layout) (slot EmptyRootArguments.i1))
    (congrArg (fun row => row.value) (slot EmptyRootArguments.i2))
    (congrArg (fun row => row.layout) (slot EmptyRootArguments.i2))
    model.ghostOff model.shallow input.tracker input.enabled first model.metadata notConstructed
  have frameBorrow : args.frame.extra.borrowTracker = some {} := by
    rw [EmptyRootArgumentProperties.extra]
    exact RawRootInvocation.frame_borrow before place model.noDataRace input.tracker input.enabled
  have dead (i : Fin 25) (ne1 : i.val ≠ 1) (ne2 : i.val ≠ 2) :
      (args.frame.locals[i.val]'(args.valid i)).value = .dead := by
    rw [EmptyRootArgumentProperties.untouched raw address count i ne1 ne2,slot i]
  obtain ⟨updated,tail,properties⟩ := S03IntegerZeroInitTail.run limits current
    (S03IntegerZeroState.model input model first) place currentInput (S03IntegerZeroState.runtime input first runtime)
    distinct order headroom second tag concrete #[] args.frame {} frameBorrow #[] extras (by simp)
    args.body args.size (dead ⟨0,by decide⟩ (by decide) (by decide))
    (dead ⟨6,by decide⟩ (by decide) (by decide)) (dead ⟨13,by decide⟩ (by decide) (by decide))
    (dead ⟨14,by decide⟩ (by decide) (by decide)) args.noClocks args.identity args.callee
  have push := CallEntryFacts.actual_call_hooks_push_raw options () (remaining+1) span limits model.debugOff
    (⟨⟨#[]⟩,before⟩ : RootState) (.memory place) thread active noCache
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span #[] raw.frame rawMachine
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span #[] raw.frame raw.frame rawMachine
  have control := RawRootInvocation.control before place model.noDataRace
  have preamble : raw.frame.location = .unwinding ⟨559⟩ := control.1
  have unchanged : {raw.frame with trackCallerArg := none} = raw.frame := by rw [←control.2.1]
  simp only [preamble] at unchanged
  refine ⟨updated,?_,properties⟩
  rw [RootCallCore.actual_entry_eq]
  unfold RootCallCore.core
  simp only [bind,EStateM.bind]
  unfold CallEntryFacts.config at push
  rw [push,RawRootInvocation.raw_eq #[] before place model.noDataRace]
  simp only [EStateM.bind]
  rw [getFrame]
  simp only [EStateM.bind,preamble,pure,EStateM.pure]
  rw [unchanged,setFrame]
  simp only [EStateM.bind]
  rw [arguments]
  simp only [EStateM.bind]
  exact tail

end
end DuplicatePrefix.S03IntegerZeroInit
