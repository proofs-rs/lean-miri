import duplicate_prefix.S03ReturnWildcardProtectionRaw
import duplicate_prefix.S03EmptyPopFactsWildcardRange
import duplicate_prefix.S03EmptyWildcardConstructorFacts

namespace DuplicatePrefix.S03EmptyWildcardRetagFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
open TypedBorrowSteps ReferenceBorrowDriver
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual configured wildcard return-protection Read/root construction
also retains the original empty argument's inactive hidden tag packet. -/
theorem retag
    {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (budget : Nat) (before : Before) (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (headroom : input.entry.allocation.extra.nodes.size+1 < 65536)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (wildcard : input.pointer.provenance = .wildcard)
    (zeroTag : BorTag) (zeroIndex : UniIndex) (zero : S03EmptyTagState.Data input.entry.allocation.extra zeroTag zeroIndex)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame) :
    ∃ tree,
      (      let global := registeredGlobal (allocatedTracker input.tracker fresh) input.tracker.global.nextPointerTag
      TypedRetag.retagPlace (config options remaining span).retag budget place MachineHooks.protectionPolicy
        (Storage.withCurrent frames frame before) =
        .ok (TypedRetagGeneric.retaggedPlace place input.id input.tracker.global.nextPointerTag)
          (ReturnProtection.borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry tree) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts tree global ∧
      tree.locations.size = input.entry.allocation.extra.locations.size ∧
      tree.nodes.size < 65536 ∧ tree.roots.toList.Nodup ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree ∧
      GeneralBorrowFreshRootSupportCutoff.ExposedBound tree input.tracker.global.nextPointerTag ∧
      ∃ child, tree.indexOfTag input.tracker.global.nextPointerTag = some child ∧
        tree.roots = input.entry.allocation.extra.roots.push child ∧
        Nonempty (GeneralBorrowFreshRootScopedRow.Positive tree global.protectedTags
          child child input.tracker.global.nextPointerTag input.offset 1) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin tree child .Write input.offset (input.offset+1) ∧
        ∃ node, tree.nodeAt child = some node ∧ node.tag = input.tracker.global.nextPointerTag ∧
          node.parent = none ∧ node.children = #[] ∧ node.isExposed = false) ∧
      Nonempty (S03EmptyTagState.Data tree zeroTag zeroIndex) := by
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,wildcard] at binding
  obtain ⟨source,_,_,_⟩ := binding
  have positive := input.borrow
  rw [source] at positive
  obtain ⟨selected,maximum⟩ := S05WildcardEntryBridge.wildcard_metadata _ _ input.selectedRoot input.maximum input.offset 1
    runtime.formed positive
  rw [selected,maximum] at positive
  obtain ⟨_,_,_,registeredRuntime,⟨registeredPositive⟩,tagFresh⟩ :=
    GeneralBorrowWildcardFnEntryRegistration.prepare input.entry.allocation.extra input.tracker.global borrowFrame input.id fresh
      runtime none none none input.offset 1 positive
  obtain ⟨output,actual,outputTag,outputGlobal,frameEq,readDone,childDone,afterRuntime,capacity,growth,
    rootsDistinct,child,lookup,roots,capability,activity,geometry⟩ :=
    GeneralBorrowRawWildcardFnEntryScopedResources.invoke input.entry.allocation.extra input.tracker.global
      borrowFrame input.id runtime input.offset 1 positive distinct (by omega) (by omega) fresh
  have shape := actual
  simp only [GeneralBorrowRawWildcardFnEntryRuntime.operation,TypedRetagEmpty.allocate_tag input.tracker.global fresh,
    Except.bind,Except.pure,bind,pure] at shape
  have outputEq := Except.ok.inj shape
  subst output
  let accessed := input.entry.allocation.extra.performBorrowAccessRange .wildcard (Size.ofBytes input.offset)
    (Size.ofBytes 1) .Read
    (GeneralBorrowFnEntryRegistration.registered input.tracker.global borrowFrame input.id fresh).1.protectedTags
    .VisitChildrenOfAccessed
  let final := accessed.tree.newChild (Size.ofBytes input.offset) .wildcard input.tracker.global.nextPointerTag
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes 1) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
  obtain ⟨readContract,readRuntime⟩ := GeneralBorrowSnapshotWildcardRangeRuntime.access
    input.entry.allocation.extra (GeneralBorrowFnEntryRegistration.registered input.tracker.global borrowFrame input.id fresh).1
    registeredRuntime (Size.ofBytes input.offset) (Size.ofBytes 1) .Read .VisitChildrenOfAccessed input.offset 1
    registeredPositive distinct (by omega) (Nat.le_refl _) (Nat.le_refl _)
  have afterFresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping input.tracker.global.nextPointerTag := by
    rw [readContract.tags]
    exact tagFresh
  have nodeRoom : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [readContract.nodes];omega
  obtain ⟨afterReadZero⟩ := S03EmptyPopFactsWildcardRange.read_data input.entry.allocation.extra
    (GeneralBorrowFnEntryRegistration.registered input.tracker.global borrowFrame input.id fresh).1 registeredRuntime
    input.offset 1 registeredPositive zeroTag zeroIndex zero
  have bounds : input.offset.toNat+1 ≤ accessed.tree.locations.size.bytes.toNat := by
    rw [readContract.capacity]
    exact registeredPositive.bounds
  obtain ⟨_,⟨afterConstructZero⟩⟩ := S03EmptyWildcardConstructorFacts.construct accessed.tree
    (GeneralBorrowFnEntryRegistration.registered input.tracker.global borrowFrame input.id fresh).1 readRuntime
    input.tracker.global.nextPointerTag afterFresh nodeRoom input.offset 1 (by decide) bounds zeroTag zeroIndex afterReadZero
  obtain ⟨mapping,index,inserted,_,vacant,_⟩ := GeneralBorrowWildcardConstructorSlot.select accessed.tree
    (GeneralBorrowFnEntryRegistration.registered input.tracker.global borrowFrame input.id fresh).1 readRuntime
    input.tracker.global.nextPointerTag afterFresh nodeRoom (.ReservedFrz false) .None
  have readNodes := readContract.nodes
  change accessed.tree.nodes = input.entry.allocation.extra.nodes at readNodes
  have readOrder := GeneralBorrowParentTagInvariant.nodes_frame _ _ readNodes order
  obtain ⟨depth⟩ := readRuntime.formed.depth
  have finalOrder := GeneralBorrowWildcardChildCausalOrder.inserted_order accessed.tree depth readOrder
    input.tracker.global.nextPointerTag mapping index inserted vacant (Size.ofBytes input.offset)
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes 1) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
  have finalExposed := S03ReturnWildcardProtectionRaw.exposed_of_positive final.tree _ afterRuntime child child input.tracker.global.nextPointerTag input.offset
    (Classical.choice capability)
  obtain ⟨ctx⟩ := ActualRetagContext.exists_context options remaining span model.preciseOff model.implicitOff
  refine ⟨final.tree,⟨?_,?_,capacity,Nat.lt_of_le_of_lt growth headroom,rootsDistinct,finalOrder,finalExposed,child,lookup,roots,?_,?_,geometry⟩,⟨afterConstructZero⟩⟩
  · apply S04ReturnWildcardProtection.retag_from_tree options remaining span ctx budget before place input wildcard frames frame borrowFrame
      frameBorrow fresh model.noDataRace accessed.tree final.tree
    · simp only [accessed,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker]
    · simpa only [GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker] using readDone
    · have eq := S04ReturnProtection.child_record _ childDone
      simpa only [final,accessed,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,MachineHooks.protectionPolicy,Option.isSome] using eq
  · simpa only [final,accessed,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker] using afterRuntime
  · simpa only [final,accessed,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker] using capability
  · simpa only [final,accessed,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker] using activity


end
end DuplicatePrefix.S03EmptyWildcardRetagFacts
