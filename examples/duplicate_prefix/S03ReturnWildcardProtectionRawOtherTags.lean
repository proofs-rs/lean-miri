import duplicate_prefix.S02WildcardReturnConstructorOtherTag
import duplicate_prefix.S04ReturnWildcardProtection
import duplicate_prefix.S04ReturnRetaggedInput
import duplicate_prefix.S04ProtectUninitScopedWrite
import duplicate_prefix.S04ProtectUninit
import duplicate_prefix.GeneralBorrowRawWildcardFnEntryScopedResources
import duplicate_prefix.GeneralBorrowWildcardChildCausalOrder

namespace DuplicatePrefix.S03ReturnWildcardProtectionRawOtherTags
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
open TypedBorrowSteps ReferenceBorrowDriver
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The exposed bound in a scoped positive packet is structural, so reading
one physically covered owner row recovers it for the whole tree. -/
theorem exposed_of_positive (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (source selected : UniIndex) (tag : BorTag) (offset : UInt64)
    (positive : GeneralBorrowFreshRootScopedRow.Positive tree global.protectedTags source selected tag offset 1) :
    GeneralBorrowFreshRootSupportCutoff.ExposedBound tree tag := by
  have bounds := positive.base.bounds
  have inside : offset.toNat < tree.locations.size.bytes.toNat := by simp only [UInt64.toNat_one] at bounds;omega
  obtain ⟨position,valid,start,stop⟩ := GeneralRangeMapGeometry.covered tree.locations runtime.formed.well offset inside
  have fits : offset.toNat+1 < 2^64 := by have bound := tree.locations.size.bytes.toNat_lt;simp only [UInt64.toNat_one] at bounds;omega
  have sum : (offset+1).toNat = offset.toNat+1 := by rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt fits]
  obtain ⟨row⟩ := positive.rows position valid (by omega) (by rw [sum];omega) stop
  exact row.exposed

/-- Configured wildcard return-destination protection from CURRENT raw input.
The explicit scoped packet retains the original exposed-support cutoff for
later wildcard restoration, including when newer hidden helpers are inserted. -/
theorem retag_other_tags
    {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (budget : Nat) (before : Before) (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (headroom : input.entry.allocation.extra.nodes.size+1 < 65536)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (wildcard : input.pointer.provenance = .wildcard)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame) :
    ∃ tree,
      let global := registeredGlobal (allocatedTracker input.tracker fresh) input.tracker.global.nextPointerTag
      TypedRetag.retagPlace (config options remaining span).retag budget place MachineHooks.protectionPolicy
        (Storage.withCurrent frames frame before) =
        .ok (TypedRetagGeneric.retaggedPlace place input.id input.tracker.global.nextPointerTag)
          (ReturnProtection.borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry tree) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts tree global ∧
      tree.locations.size = input.entry.allocation.extra.locations.size ∧
      tree.nodes.size < 65536 ∧ tree.roots.toList.Nodup ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree ∧
      GeneralBorrowFreshRootSupportCutoff.ExposedBound tree input.tracker.global.nextPointerTag ∧
      (∀ query, input.tracker.global.nextPointerTag ≠ query →
        tree.indexOfTag query = input.entry.allocation.extra.indexOfTag query) ∧
      ∃ child, tree.indexOfTag input.tracker.global.nextPointerTag = some child ∧
        tree.roots = input.entry.allocation.extra.roots.push child ∧
        Nonempty (GeneralBorrowFreshRootScopedRow.Positive tree global.protectedTags
          child child input.tracker.global.nextPointerTag input.offset 1) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin tree child .Write input.offset (input.offset+1) ∧
        ∃ node, tree.nodeAt child = some node ∧ node.tag = input.tracker.global.nextPointerTag ∧
          node.parent = none ∧ node.children = #[] ∧ node.isExposed = false := by
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
  have finalExposed := exposed_of_positive final.tree _ afterRuntime child child input.tracker.global.nextPointerTag input.offset
    (Classical.choice capability)
  have finalOther : ∀ query, input.tracker.global.nextPointerTag ≠ query →
      final.tree.indexOfTag query = input.entry.allocation.extra.indexOfTag query := by
    intro query different
    have nonzero : (1 : UInt64) ≠ 0 := by decide
    have readBounds : input.offset.toNat + (1 : UInt64).toNat ≤ accessed.tree.locations.size.bytes.toNat := by
      rw [readContract.capacity]
      exact positive.bounds
    have other := S02WildcardReturnConstructorOtherTag.preserved accessed.tree
      (GeneralBorrowFnEntryRegistration.registered input.tracker.global borrowFrame input.id fresh).1
      readRuntime input.tracker.global.nextPointerTag query different afterFresh nodeRoom
      input.offset 1 nonzero readBounds
    change final.tree.indexOfTag query = input.entry.allocation.extra.indexOfTag query
    calc
      final.tree.indexOfTag query = accessed.tree.indexOfTag query := other
      _ = input.entry.allocation.extra.indexOfTag query := by
        unfold BorrowTree.indexOfTag
        rw [readContract.tags]
  obtain ⟨ctx⟩ := ActualRetagContext.exists_context options remaining span model.preciseOff model.implicitOff
  refine ⟨final.tree,?_,?_,capacity,Nat.lt_of_le_of_lt growth headroom,rootsDistinct,finalOrder,finalExposed,finalOther,child,lookup,roots,?_,?_,geometry⟩
  · apply S04ReturnWildcardProtection.retag_from_tree options remaining span ctx budget before place input wildcard frames frame borrowFrame
      frameBorrow fresh model.noDataRace accessed.tree final.tree
    · simp only [accessed,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker]
    · simpa only [GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker] using readDone
    · have eq := S04ReturnProtection.child_record _ childDone
      simpa only [final,accessed,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,MachineHooks.protectionPolicy,Option.isSome] using eq
  · simpa only [final,accessed,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker] using afterRuntime
  · simpa only [final,accessed,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker] using capability
  · simpa only [final,accessed,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker] using activity

/-- Actual configured protection and physical uninitializing store for an
original wildcard destination. Runtime, scoped permissions and root geometry
on the resulting allocation are derived from the original input. -/
theorem invoke_other_tags
    {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (budget : Nat) (before : Before) (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (headroom : input.entry.allocation.extra.nodes.size+1 < 65536)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (wildcard : input.pointer.provenance = .wildcard)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,sync⟩))
    (outside : ∀ row ∈ sync,
      row.1.bytes.toNat < input.offset.toNat ∨ input.offset.toNat+1 ≤ row.1.bytes.toNat) :
    ∃ tree updated,
      let global := registeredGlobal (allocatedTracker input.tracker fresh) input.tracker.global.nextPointerTag
      let written := (tree.performBorrowAccessRange (.concrete input.tracker.global.nextPointerTag)
        (Size.ofBytes input.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
      TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag budget place
        (Storage.withCurrent frames frame before) =
        .ok () (S04ProtectUninit.finished before place input frames frame borrowFrame fresh tree updated) ∧
      updated.extra = written ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut ∧
      InitMaskCopy.WellFormed updated.initializationMask ∧
      updated.initializationMask.len = input.entry.allocation.initializationMask.len ∧
      (∀ row ∈ updated.provenanceMap.ptrs, row.1.bytes.toNat+8≤updated.len) ∧
      written.locations.size = input.entry.allocation.extra.locations.size ∧
      DuplicatePrefixBorrowContract.RuntimeFacts written global ∧
      written.nodes.size < 65536 ∧ written.roots.toList.Nodup ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder written ∧
      GeneralBorrowFreshRootSupportCutoff.ExposedBound written input.tracker.global.nextPointerTag ∧
      (∀ query, input.tracker.global.nextPointerTag ≠ query →
        written.indexOfTag query = input.entry.allocation.extra.indexOfTag query) ∧
      ∃ child, written.indexOfTag input.tracker.global.nextPointerTag = some child ∧
        written.roots = input.entry.allocation.extra.roots.push child ∧
        Nonempty (GeneralBorrowFreshRootScopedRow.Positive written global.protectedTags
          child child input.tracker.global.nextPointerTag input.offset 1) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin written child .Write input.offset (input.offset+1) ∧
        ∃ node, written.nodeAt child = some node ∧ node.tag = input.tracker.global.nextPointerTag ∧
          node.parent = none ∧ node.children = #[] ∧ node.isExposed = false := by
  obtain ⟨tree,actual,post,capacity,short,rootsDistinct,treeOrder,treeExposed,treeOther,child,tagged,roots,⟨positive⟩,active,geometry⟩ :=
    retag_other_tags budget before model place input runtime distinct order headroom fresh wildcard frames frame borrowFrame frameBorrow
  let global := registeredGlobal (allocatedTracker input.tracker fresh) input.tracker.global.nextPointerTag
  let current := ReturnProtection.borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry tree
  let next := S04ReturnRetaggedInput.from_borrowed input frames frame borrowFrame fresh tree child (some child)
    (some input.tracker.global.nextPointerTag) tagged capacity positive.base
  obtain ⟨updated,write,extra,bytes,length,mutable,maskWf,maskLen,pointerBounds,afterRuntime,afterTags,afterPositive,afterActive⟩ :=
    S04ProtectUninitScopedWrite.from_current (options := options) (remaining := remaining) span current _ next post rootsDistinct
      short input.tracker.global.nextPointerTag child tagged positive rfl model.noDataRace model.noBackend sync extras outside
  let after := S04ProtectUninit.finished before place input frames frame borrowFrame fresh tree updated
  have configuredWrite : (config options remaining span).retag.writeUninit
      (TypedRetagGeneric.retaggedPlace place input.id input.tracker.global.nextPointerTag) current = .ok () after := by
    obtain ⟨ctx⟩ := ActualRetagContext.exists_context options remaining span model.preciseOff model.implicitOff
    rw [ctx.construction]
    change (do
      let access ← ValidityMachine.scopedAccess (config options remaining span).access
      PlaceMachine.writeMemory access (fun _ => false) .uninit
        (TypedRetagGeneric.retaggedPlace place input.id input.tracker.global.nextPointerTag)) current = .ok () after
    have accessGhost : (config options remaining span).access.ghostMode = false := by
      rw [(DuplicatePrefixPhysicalContexts.canonical options remaining span).accessEq]
      rfl
    have scope := S04ProtectUninitWrite.scopedAccess_of_not_ghost
      (config options remaining span).access current accessGhost model.ghostOff
    simp only [bind,EStateM.bind,scope]
    exact write
  let written := (tree.performBorrowAccessRange (.concrete input.tracker.global.nextPointerTag)
    (Size.ofBytes input.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
  have framed : written.nodes = tree.nodes ∧ written.roots = tree.roots ∧ written.locations.size = tree.locations.size := by
    obtain ⟨contract,_,_⟩ := GeneralBorrowFreshRootScopedRange.access_runtime_kind tree global post
      input.tracker.global.nextPointerTag child child input.tracker.global.nextPointerTag tagged
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write .VisitChildrenOfAccessed input.offset 1 positive rootsDistinct short
      (Nat.le_refl _) (Nat.le_refl _)
    exact ⟨contract.nodes,contract.roots,contract.capacity⟩
  have writtenOrder := GeneralBorrowParentTagInvariant.nodes_frame tree written framed.1 treeOrder
  have writtenExposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound written input.tracker.global.nextPointerTag := by
    intro index value found exposed
    change written.nodes.get index = some value at found
    rw [framed.1] at found
    exact treeExposed index value found exposed
  have writtenOther : ∀ query, input.tracker.global.nextPointerTag ≠ query →
      written.indexOfTag query = input.entry.allocation.extra.indexOfTag query := by
    intro query different
    have writeFrame := GeneralBorrowFreshReadFrame.frame tree
      (.concrete input.tracker.global.nextPointerTag) (Size.ofBytes input.offset) (Size.ofBytes 1)
      .Write global.protectedTags .VisitChildrenOfAccessed
    unfold BorrowTree.indexOfTag
    rw [congrArg BorrowTree.tagMapping writeFrame]
    exact treeOther query different
  refine ⟨tree,updated,?_,extra,bytes,length,mutable,maskWf,maskLen,pointerBounds,framed.2.2.trans capacity,afterRuntime,?_,?_,writtenOrder,writtenExposed,writtenOther,child,?_,?_,afterPositive,afterActive child active,?_⟩
  · unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace
    simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,Storage.withCurrent,
      input.enabled,Option.isSome_some,↓reduceIte]
    erw [actual]
    exact configuredWrite
  · rw [framed.1]
    exact short
  · rw [framed.2.1]
    exact rootsDistinct
  · unfold BorrowTree.indexOfTag
    change (next.entry.allocation.extra.performBorrowAccessRange (.concrete input.tracker.global.nextPointerTag)
      (Size.ofBytes next.offset) (Size.ofBytes 1) .Write next.tracker.global.protectedTags
      .VisitChildrenOfAccessed).tree.tagMapping.get _ = _
    rw [afterTags]
    exact tagged
  · rw [framed.2.1]
    exact roots
  · obtain ⟨node,present,same,parentless,leaf,hidden⟩ := geometry
    exact ⟨node,by change written.nodes.get child = _;rw [framed.1];exact present,same,parentless,leaf,hidden⟩

end
end DuplicatePrefix.S03ReturnWildcardProtectionRawOtherTags

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S03ReturnWildcardProtectionRawOtherTags.retag_other_tags,
      ``DuplicatePrefix.S03ReturnWildcardProtectionRawOtherTags.invoke_other_tags] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved wildcard protect old-tag dependency {dependency}"
