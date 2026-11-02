import duplicate_prefix.S03WildcardMissEntry
import duplicate_prefix.S03WildcardMissFrame
import duplicate_prefix.S03WildcardMissArgumentProperties
import duplicate_prefix.S03ReturnInitTail
import duplicate_prefix.S03ReturnWildcardProtectionRaw
import duplicate_prefix.S03IntegerZeroFrame

namespace DuplicatePrefix.S03WildcardMissWildcardInit
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def frame (target : TargetDataLayout) {before : Before} {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place) (race : before.dataRace = none)
    (address count : UInt64) (first : input.tracker.global.nextPointerTag.value < 18446744073709551615) :=
  S03WildcardMissFrame.installed (RawRootInvocation.root before place race) target address count {} input.id
    (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag

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
    (tree : BorrowTree) :=
  (tree.performBorrowAccessRange (.concrete (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag)
    (Size.ofBytes input.offset) (Size.ofBytes 1) .Write (global input first second).protectedTags .VisitChildrenOfAccessed).tree

def installed (target : TargetDataLayout) {before : Before} {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place) (race : before.dataRace = none)
    (address count : UInt64) (first : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (second : (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag.value < 18446744073709551615)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree) : RootState :=
  let args := S03WildcardMissArguments.result (RawRootInvocation.root before place race) target address count
  Storage.withCurrent #[] (frame target input race address count first)
    (S04ProtectUninit.finished (S03IntegerZeroState.argumentsMachine before input.tracker first) place
      (S03IntegerZeroState.input input first) #[] {args.frame with location := .unwinding ⟨601⟩} {}
      second tree updated).machine

/-- Original unresolved wildcard argument plus actual wildcard destination
protection in initStackFrame. Every post-state permission and physical fact is
derived from initial inputs; source argument/frame setup is shared. -/
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
    (wildcard : input.pointer.provenance = .wildcard)
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
    ∃ tree updated,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (S03WildcardMissArguments.first (config options remaining span).access.runtime.base address),.Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (installed (config options remaining span).access.runtime.base input model.noDataRace address count first second tree updated) ∧
      updated.extra = written input first second tree ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut ∧
      InitMaskCopy.WellFormed updated.initializationMask ∧
      updated.initializationMask.len = input.entry.allocation.initializationMask.len ∧
      (∀ row ∈ updated.provenanceMap.ptrs, row.1.bytes.toNat+8≤updated.len) ∧
      (written input first second tree).locations.size = input.entry.allocation.extra.locations.size ∧
      DuplicatePrefixBorrowContract.RuntimeFacts (written input first second tree) (global input first second) ∧
      (written input first second tree).nodes.size < 65536 ∧ (written input first second tree).roots.toList.Nodup ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder (written input first second tree) ∧
      GeneralBorrowFreshRootSupportCutoff.ExposedBound (written input first second tree)
        (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag ∧
      ∃ child, (written input first second tree).indexOfTag
          (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag = some child ∧
        (written input first second tree).roots = input.entry.allocation.extra.roots.push child ∧
        Nonempty (GeneralBorrowFreshRootScopedRow.Positive (written input first second tree) (global input first second).protectedTags
          child child (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag input.offset 1) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin (written input first second tree) child .Write input.offset (input.offset+1) ∧
        ∃ node, (written input first second tree).nodeAt child = some node ∧
          node.tag = (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag ∧
          node.parent = none ∧ node.children = #[] ∧ node.isExposed = false := by
  let root := RawRootInvocation.root before place model.noDataRace
  let args := S03WildcardMissArguments.result root (config options remaining span).access.runtime.base address count
  let current := S03IntegerZeroState.argumentsMachine before input.tracker first
  let currentInput := S03IntegerZeroState.input input first
  have raw : root.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
    RawRootInvocation.locals before place model.noDataRace
  have slot (i : Fin 25) : (root.frame.locals[i.val]'(root.valid i)) = ⟨.dead,none⟩ := by
    simp only [raw,Array.getElem_replicate]
  have dead (i : Fin 25) (ne1 : i.val ≠ 1) (ne2 : i.val ≠ 2) :
      (args.frame.locals[i.val]'(args.valid i)).value = .dead := by
    rw [S03WildcardMissArgumentProperties.untouched root (config options remaining span).access.runtime.base address count i ne1 ne2,slot i]
  have frameBorrow : args.frame.extra.borrowTracker = some {} := by
    rw [S03WildcardMissArgumentProperties.extra]
    exact RawRootInvocation.frame_borrow before place model.noDataRace input.tracker input.enabled
  let currentModel := S03IntegerZeroState.model input model first
  obtain ⟨tree,updated,protect,properties⟩ := S03ReturnWildcardProtectionRaw.invoke limits.retag current currentModel place currentInput
    (S03IntegerZeroState.runtime input first runtime) distinct order headroom second wildcard #[]
    {args.frame with location := .unwinding ⟨601⟩} {} frameBorrow #[] extras (by simp)
  have tail := S03ReturnInitTail.after_protection limits current currentModel place currentInput #[] args.frame {}
    frameBorrow second tree updated protect args.body args.size
    (dead ⟨0,by decide⟩ (by decide) (by decide)) (dead ⟨6,by decide⟩ (by decide) (by decide))
    (dead ⟨13,by decide⟩ (by decide) (by decide)) (dead ⟨14,by decide⟩ (by decide) (by decide))
    args.noClocks args.identity args.callee
  have entry := S03WildcardMissEntry.after_tail limits before model place input first address count nonzero addressMode miss dynamicFuel validityFuel
    dynamicEq validityEq notConstructed thread active noCache _ tail
  exact ⟨tree,updated,entry,properties⟩

end
end DuplicatePrefix.S03WildcardMissWildcardInit
