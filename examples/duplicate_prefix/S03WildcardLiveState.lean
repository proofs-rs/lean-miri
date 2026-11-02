import duplicate_prefix.S03LiveEmptyState
import duplicate_prefix.WildcardPoolHitRootArgumentScope
import duplicate_prefix.GeneralBorrowParentTagConstructors

namespace DuplicatePrefix.S03WildcardLiveState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

def slot (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (short : tree.nodes.size < 65536) : WildcardHitPoolRoot.Slot tree :=
  WildcardHitPoolRoot.factory tree runtime.formed.allocator.pool runtime.formed.allocator.accounting
    (by have accounting := runtime.formed.allocator.accounting;unfold GeneralBorrowFreshStagePool.Accounting at accounting;omega)

abbrev next (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) := S03LiveEmptyState.next tracker fresh

def argumentsMachine {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (rootSlot : WildcardHitPoolRoot.Slot original.entry.allocation.extra) : Before :=
  WildcardPoolHitRootArgumentScope.resultMachine (RawRootInvocation.machine #[] before) original.tracker fresh
    original.id original.entry rootSlot

/-- The actual hidden zero root preserves original concrete return binding
and every byte/address field while changing the original allocation's tree. -/
def input {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (rootSlot : WildcardHitPoolRoot.Slot original.entry.allocation.extra)
    (tag : BorTag) (concrete : original.pointer.provenance = .concrete original.id tag)
    (tagFresh : GeneralBorrowTagMap.Fresh original.entry.allocation.extra.tagMapping original.tracker.global.nextPointerTag)
    (positive : DuplicatePrefixBorrowAuthorization.Positive (rootSlot.after original.tracker.global.nextPointerTag)
      (next original.tracker fresh).global.protectedTags original.source original.selectedRoot original.maximum original.offset 1) :
    DuplicatePrefixReturnPlaceInput.Input (argumentsMachine original fresh rootSlot) place := by
  let tree := rootSlot.after original.tracker.global.nextPointerTag
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {original.entry with allocation := original.entry.allocation.setExtra tree}
  refine {
    tracker := next original.tracker fresh, enabled := rfl,
    pointer := original.pointer,physicalPointer := original.physicalPointer,layout := original.layout,aligned := original.aligned,
    id := original.id,entry := entry,base := original.base,offset := original.offset,capacity := original.capacity,
    live := ?_,cachedBase := original.cachedBase,pointerAddress := original.pointerAddress,nonnull := original.nonnull,
    addressFits := original.addressFits,bounds := original.bounds,size := original.size,bytes := original.bytes,mutable := original.mutable,
    maskValid := original.maskValid,maskLength := original.maskLength,provenanceMap := original.provenanceMap,
    borrowSize := original.borrowSize,source := original.source,selectedRoot := original.selectedRoot,maximum := original.maximum,
    binding := ?_,borrow := positive }
  · exact MemoryCopyBridge.live_lookup_replaced before.memory original.id entry
  · have binding := original.binding
    simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
    obtain ⟨idEq,anchor,source,tagged⟩ := binding
    have different := S03EmptyReturnConstructorFacts.fresh_ne original.entry.allocation.extra original.tracker.global.nextPointerTag
      tag anchor tagFresh tagged
    change DuplicatePrefixReferenceInput.Binding _ original.pointer _ _ _ tree original.source
    simp only [DuplicatePrefixReferenceInput.Binding,concrete]
    refine ⟨True.intro,anchor,source,?_⟩
    exact GeneralBorrowTagMap.pushed_get_old original.entry.allocation.extra.tagMapping original.tracker.global.nextPointerTag tag
      different rootSlot.index rootSlot.free |>.trans tagged

theorem model {options : EvalConfigurationCore.Options} {remaining : Nat}
    {span : PreparedContracts.FixedSpanQuery} {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (initial : DuplicatePrefixCallModel.Model options remaining span before)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (rootSlot : WildcardHitPoolRoot.Slot original.entry.allocation.extra) :
    DuplicatePrefixCallModel.Model options (remaining+1) span (argumentsMachine original fresh rootSlot) := by
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

/-- Wildcard zero FnEntry yields an actual hidden inactive root, runtime and
the original return observer on the same allocator-selected tree. -/
theorem facts {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts original.entry.allocation.extra original.tracker.global)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (rootSlot : WildcardHitPoolRoot.Slot original.entry.allocation.extra)
    (short : original.entry.allocation.extra.nodes.size+2 < 65536)
    (distinct : original.entry.allocation.extra.roots.toList.Nodup)
    (ordered : GeneralBorrowWildcardParentTagOrder.ParentTagOrder original.entry.allocation.extra) :
    let tree := rootSlot.after original.tracker.global.nextPointerTag
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive tree (next original.tracker fresh).global.protectedTags
      original.source original.selectedRoot original.maximum original.offset 1) ∧
    DuplicatePrefixBorrowContract.RuntimeFacts tree (next original.tracker fresh).global ∧
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree ∧ tree.roots.toList.Nodup ∧ tree.nodes.size+1 < 65536 ∧
    Nonempty (S03EmptyTagState.Data tree original.tracker.global.nextPointerTag rootSlot.index) ∧
    GeneralBorrowTagMap.Fresh original.entry.allocation.extra.tagMapping original.tracker.global.nextPointerTag ∧
    ∀ anchor, original.source = some anchor → rootSlot.index ≠ anchor := by
  have packet := S03EmptyFnEntryFacts.wildcard_registered original.entry.allocation.extra original.tracker.global {} original.id runtime
    (by omega) fresh 0 original.source original.selectedRoot original.maximum original.offset 1 original.borrow
  have tagFresh := GeneralBorrowParentTagInvariant.fresh _ _ runtime
  rw [rootSlot.child original.tracker.global.nextPointerTag tagFresh 0] at packet
  obtain ⟨_,_,_,_,positive,current,_⟩ := packet
  have order := GeneralBorrowParentTagConstructors.installed_root original.entry.allocation.extra
    (Classical.choice runtime.formed.depth) ordered (rootSlot.mapping original.tracker.global.nextPointerTag) rootSlot.index rootSlot.vacant
    original.tracker.global.nextPointerTag (.ReservedFrz false) .None
  have growth := rootSlot.size original.tracker.global.nextPointerTag
  have bound : rootSlot.growth ≤ 1 := by cases rootSlot <;> simp [WildcardHitPoolRoot.Slot.growth]
  have outside : rootSlot.index ∉ original.entry.allocation.extra.roots.toList := by
    intro member
    obtain ⟨node,present,parentless⟩ := runtime.formed.rootNodes rootSlot.index member
    rw [rootSlot.vacant] at present
    contradiction
  have afterDistinct : (rootSlot.after original.tracker.global.nextPointerTag).roots.toList.Nodup := by
    change (original.entry.allocation.extra.roots.push rootSlot.index).toList.Nodup
    rw [Array.toList_push,List.nodup_append]
    refine ⟨?_,by simp,?_⟩
    · exact distinct
    · intro old member query singleton same
      have eq : query = rootSlot.index := by simpa using singleton
      subst query
      subst old
      exact outside member
  refine ⟨positive,current,order,afterDistinct,by omega,
    ⟨S03EmptyFnEntryFacts.wildcard_data _ rootSlot _ tagFresh (DuplicatePrefixBorrowContract.vacant_clean runtime)⟩,tagFresh,?_⟩
  intro anchor source same
  obtain ⟨node,present⟩ := original.borrow.sourcePresent anchor source
  rw [←same,show original.entry.allocation.extra.nodeAt rootSlot.index=none from rootSlot.vacant] at present
  cases present

end
end DuplicatePrefix.S03WildcardLiveState
