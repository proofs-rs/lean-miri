import duplicate_prefix.S03EmptyFnEntryFacts
import duplicate_prefix.S03EmptyProtectUninit
import duplicate_prefix.S03IntegerZeroState
import duplicate_prefix.ConcretePoolRootArgumentScope
import duplicate_prefix.ConcreteEmptyRuntimeEntry
import duplicate_prefix.GeneralBorrowFreshParentTagOrder
import duplicate_prefix.GeneralBorrowParentTagInvariant

namespace DuplicatePrefix.S03LiveEmptyState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

abbrev next (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) : MachineHooks.BorrowState :=
  ⟨TypedRetagGeneric.protectedGlobal tracker.global fresh,tracker.retagMode⟩

def argumentsMachine {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag) (slot : ConcreteEmptyPoolEntry.Input original.entry.allocation.extra parentTag original.tracker.global.nextPointerTag) : Before :=
  ConcretePoolRootArgumentScope.resultMachine (RawRootInvocation.machine #[] before) original.tracker fresh
    original.id original.entry parentTag slot

/-- Zero argument retag changes only the tree and tracker of the shared backing
allocation. The original concrete return pointer and physical metadata form the
current destination Input with the observer capability derived by construction. -/
def input {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag) (slot : ConcreteEmptyPoolEntry.Input original.entry.allocation.extra parentTag original.tracker.global.nextPointerTag)
    (tag : BorTag) (concrete : original.pointer.provenance = .concrete original.id tag)
    (positive : DuplicatePrefixBorrowAuthorization.Positive slot.after (next original.tracker fresh).global.protectedTags
      original.source original.selectedRoot original.maximum original.offset 1) :
    DuplicatePrefixReturnPlaceInput.Input (argumentsMachine original fresh parentTag slot) place := by
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {original.entry with allocation := original.entry.allocation.setExtra slot.after}
  refine {
    tracker := next original.tracker fresh, enabled := rfl,
    pointer := original.pointer,physicalPointer := original.physicalPointer,layout := original.layout,aligned := original.aligned,
    id := original.id,entry := entry,base := original.base,offset := original.offset,capacity := original.capacity,
    live := ?_,cachedBase := original.cachedBase,pointerAddress := original.pointerAddress,nonnull := original.nonnull,
    addressFits := original.addressFits,bounds := original.bounds,size := original.size,bytes := original.bytes,mutable := original.mutable,
    maskValid := original.maskValid,maskLength := original.maskLength,provenanceMap := original.provenanceMap,
    borrowSize := ?_,source := original.source,selectedRoot := original.selectedRoot,maximum := original.maximum,
    binding := ?_,borrow := positive }
  · exact MemoryCopyBridge.live_lookup_replaced before.memory original.id entry
  · change slot.after.locations.size.bytes = original.capacity
    rw [S04ZeroChildMetadata.capacity _ _ _ slot]
    exact original.borrowSize
  · have binding := original.binding
    simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
    obtain ⟨idEq,anchor,source,tagged⟩ := binding
    have different := S03EmptyReturnConstructorFacts.fresh_ne original.entry.allocation.extra original.tracker.global.nextPointerTag
      tag anchor slot.fresh tagged
    change DuplicatePrefixReferenceInput.Binding _ original.pointer _ _ _ slot.after original.source
    simp only [DuplicatePrefixReferenceInput.Binding,concrete]
    refine ⟨True.intro,anchor,source,?_⟩
    unfold BorrowTree.indexOfTag
    rw [slot.mapping_after]
    exact (GeneralBorrowTagMap.pushed_get_old original.entry.allocation.extra.tagMapping original.tracker.global.nextPointerTag tag
      different slot.index slot.free).trans tagged

/-- Current model facts are transported through the actual raw frame push and
live zero argument retag; control/accounting projections are kept explicitly. -/
theorem model {options : EvalConfigurationCore.Options} {remaining : Nat}
    {span : PreparedContracts.FixedSpanQuery} {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (initial : DuplicatePrefixCallModel.Model options remaining span before)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag) (slot : ConcreteEmptyPoolEntry.Input original.entry.allocation.extra parentTag original.tracker.global.nextPointerTag) :
    DuplicatePrefixCallModel.Model options (remaining+1) span (argumentsMachine original fresh parentTag slot) := by
  have shifted := S03IntegerZeroState.retime initial (remaining+1)
  obtain ⟨tracker,enabled,mode⟩ := initial.defaultTracker
  have same : tracker = original.tracker := Option.some.inj (enabled.symm.trans original.enabled)
  subst tracker
  refine {shifted with defaultTracker := ⟨next original.tracker fresh,rfl,mode⟩,unchecked := ?_,noGc := ?_}
  · change ((PreparedContracts.actualConfig options () (remaining+1+1) span).terminators.getControl
      (RawRootInvocation.machine #[] before).user).checkedArithmetic = false
    rw [RootZeroInvocationState.raw_control]
    exact shifted.unchecked
  · change ((PreparedContracts.actualConfig options () (remaining+1+1) span).terminators.getControl
      (RawRootInvocation.machine #[] before).user).gcInterval = 0
    rw [RootZeroInvocationState.raw_control]
    exact shifted.noGc

/-- Full current-state packet for the actual arbitrary-forest ZERO constructor.
The return observer and zero inactivity are produced, and residual node room
follows from the constructor's concrete growth bound. -/
theorem facts {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts original.entry.allocation.extra original.tracker.global)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag) (slot : ConcreteEmptyPoolEntry.Input original.entry.allocation.extra parentTag original.tracker.global.nextPointerTag)
    (short : original.entry.allocation.extra.nodes.size+2 < 65536)
    (ordered : GeneralBorrowWildcardParentTagOrder.ParentTagOrder original.entry.allocation.extra) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive slot.after (next original.tracker fresh).global.protectedTags
      original.source original.selectedRoot original.maximum original.offset 1) ∧
    DuplicatePrefixBorrowContract.RuntimeFacts slot.after (next original.tracker fresh).global ∧
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder slot.after ∧
    slot.after.roots = original.entry.allocation.extra.roots ∧ slot.after.nodes.size+1 < 65536 ∧
    Nonempty (S03EmptyTagState.Data slot.after original.tracker.global.nextPointerTag slot.index) ∧
    ∀ anchor, original.source = some anchor → slot.index ≠ anchor := by
  have packet := S03EmptyFnEntryFacts.concrete_complete original.entry.allocation.extra original.tracker.global {} original.id runtime
    parentTag slot.parent slot.parentNode slot.tagged slot.present (by omega) fresh 0
    original.source original.selectedRoot original.maximum original.offset 1 original.borrow
  rw [slot.child 0] at packet
  obtain ⟨_,_,_,_,positive,current,_,_,_⟩ := packet
  have parentOrder : slot.parentNode.tag.value ≤ original.tracker.global.nextPointerTag.value :=
    UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp
      (GeneralBorrowParentTagInvariant.parent_below_fresh _ _ runtime slot.parent slot.parentNode slot.present)))
  have order := GeneralBorrowFreshParentTagOrder.staged_order _ slot.depth ordered slot.index slot.parent slot.parentNode
    (GeneralBorrowFreshChild.child original.tracker.global.nextPointerTag slot.parent) slot.vacant slot.present rfl parentOrder
    slot.mapping original.entry.allocation.extra.locations slot.after (GeneralBorrowSifaView.preserves slot.stage slot.parent .None)
  have growth := ConcreteEmptyPoolEntryNext.node_size slot
  have bound : ConcreteEmptyPoolEntryNext.growth slot ≤ 1 := by
    cases selected : slot.slot <;> simp only [ConcreteEmptyPoolEntryNext.growth,selected] <;> omega
  refine ⟨positive,current,order,S04ZeroChildMetadata.roots _ _ _ slot,by omega,
    ⟨S03EmptyFnEntryFacts.concrete_data _ _ _ slot⟩,?_⟩
  intro anchor source same
  obtain ⟨node,present⟩ := original.borrow.sourcePresent anchor source
  rw [←same,show original.entry.allocation.extra.nodeAt slot.index=none from slot.vacant] at present
  cases present

end
end DuplicatePrefix.S03LiveEmptyState
