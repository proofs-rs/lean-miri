import duplicate_prefix.S03IntegerZeroInitTail
import duplicate_prefix.S03WildcardMissEntry
import duplicate_prefix.S03WildcardMissFrame
import duplicate_prefix.S03WildcardMissArgumentProperties

namespace DuplicatePrefix.S03WildcardMissConcreteInit
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

def frame (target : TargetDataLayout) {before : Before} {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place) (race : before.dataRace = none)
    (address count : UInt64) (first : input.tracker.global.nextPointerTag.value < 18446744073709551615) :=
  let args := S03WildcardMissArguments.result (RawRootInvocation.root before place race) target address count
  CallEntryFacts.doneRootFrame {TypedBorrowSteps.registeredFrame
    {args.frame with location := .unwinding ⟨601⟩} {} input.id
    (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag
      with location := .unwinding ⟨559⟩}

def installed (target : TargetDataLayout) {before : Before} {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place) (race : before.dataRace = none)
    (address count : UInt64) (first : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (second : (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag.value < 18446744073709551615)
    (tag : BorTag) (updated : Allocation Provenance BorrowTree) : RootState :=
  let args := S03WildcardMissArguments.result (RawRootInvocation.root before place race) target address count
  Storage.withCurrent #[] (frame target input race address count first)
    (S04ProtectUninit.finished (S03IntegerZeroState.argumentsMachine before input.tracker first) place
      (S03IntegerZeroState.input input first) #[] {args.frame with location := .unwinding ⟨601⟩} {}
      second (tree input first tag) updated).machine

/-- The original unresolved wildcard empty argument initStackFrame for arbitrary count,
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
    (addressMode : before.user.addresses.provenanceMode ≠ .strict)
    (miss : before.user.addresses.allocIdFromAddr address 0
      (GlobalAddressLiveErrorExclusion.lookup before.memory) = .ok none)
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
        #[.Copy (S03WildcardMissArguments.first (config options remaining span).access.runtime.base address),.Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (installed (config options remaining span).access.runtime.base input model.noDataRace address count first second tag updated) ∧
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
  let args := S03WildcardMissArguments.result raw (config options remaining span).access.runtime.base address count
  let current := S03IntegerZeroState.argumentsMachine before input.tracker first
  let currentInput := S03IntegerZeroState.input input first
  have slot (i : Fin 25) : (raw.frame.locals[i.val]'(raw.valid i)) = ⟨.dead,none⟩ := by
    have rows := congrArg (fun rows : Array (LocalState Provenance LocalLayout) => rows[i.val]?)
      (RawRootInvocation.locals before place model.noDataRace)
    have row : raw.frame.locals[i.val]? = some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
      simpa only [Array.getElem?_replicate,i.isLt,↓reduceIte] using rows
    exact Option.some.inj ((Array.getElem?_eq_getElem (raw.valid i)).symm.trans row)
  have frameBorrow : args.frame.extra.borrowTracker = some {} := by
    rw [S03WildcardMissArgumentProperties.extra]
    exact RawRootInvocation.frame_borrow before place model.noDataRace input.tracker input.enabled
  have dead (i : Fin 25) (ne1 : i.val ≠ 1) (ne2 : i.val ≠ 2) :
      (args.frame.locals[i.val]'(args.valid i)).value = .dead := by
    rw [S03WildcardMissArgumentProperties.untouched raw (config options remaining span).access.runtime.base address count i ne1 ne2,slot i]
  obtain ⟨updated,tail,properties⟩ := S03IntegerZeroInitTail.run limits current
    (S03IntegerZeroState.model input model first) place currentInput (S03IntegerZeroState.runtime input first runtime)
    distinct order headroom second tag concrete #[] args.frame {} frameBorrow #[] extras (by simp)
    args.body args.size (dead ⟨0,by decide⟩ (by decide) (by decide))
    (dead ⟨6,by decide⟩ (by decide) (by decide)) (dead ⟨13,by decide⟩ (by decide) (by decide))
    (dead ⟨14,by decide⟩ (by decide) (by decide)) args.noClocks args.identity args.callee
  have entry := S03WildcardMissEntry.after_tail limits before model place input first address count nonzero
    addressMode miss dynamicFuel validityFuel dynamicEq validityEq notConstructed thread active noCache _ tail
  exact ⟨updated,entry,properties⟩

end
end DuplicatePrefix.S03WildcardMissConcreteInit
