import duplicate_prefix.S02WildcardReturnSameSourceActivity
import duplicate_prefix.S03ReturnWildcardProtectionRawOtherTags
namespace DuplicatePrefix.S02WildcardReturnSameSourceActivityPacket
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification TypedBorrowSteps ReferenceBorrowDriver
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Current physical data executes actual wildcard protection and uninit,
retaining the disjoint source's capability, activity and old node/tag bindings
on the very allocation installed by that operation. -/
theorem invoke
    {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (budget : Nat) (before : Before) (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (headroom : input.entry.allocation.extra.nodes.size+1 < 65536)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (wildcard : input.pointer.provenance = .wildcard)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) = some (input.id,⟨none,sync⟩))
    (outsideSync : ∀ row ∈ sync, row.1.bytes.toNat < input.offset.toNat ∨ input.offset.toNat+1 ≤ row.1.bytes.toNat)
    (query selected : UniIndex) (maximum : Option BorTag) (lower width : UInt64)
    (outside : input.offset.toNat+1 ≤ lower.toNat ∨ (lower+width).toNat ≤ input.offset.toNat)
    (old : DuplicatePrefixBorrowAuthorization.Positive input.entry.allocation.extra input.tracker.global.protectedTags
      (some query) (some selected) maximum lower width)
    (node : TreeNode) (present : input.entry.allocation.extra.nodeAt query = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin input.entry.allocation.extra query .Write lower (lower+width)) :
    let registration := GeneralBorrowFnEntryRegistration.registered input.tracker.global borrowFrame input.id fresh
    let read := input.entry.allocation.extra.performBorrowAccessRange .wildcard (Size.ofBytes input.offset) (Size.ofBytes 1)
      .Read registration.1.protectedTags .VisitChildrenOfAccessed
    let tree := (read.tree.newChild (Size.ofBytes input.offset) .wildcard input.tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes 1) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree
    let written := (tree.performBorrowAccessRange (.concrete input.tracker.global.nextPointerTag)
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write registration.1.protectedTags .VisitChildrenOfAccessed).tree
    ∃ updated,
      TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag budget place
        (Storage.withCurrent frames frame before) = .ok () (S04ProtectUninit.finished before place input frames frame borrowFrame fresh tree updated) ∧
      updated.extra = written ∧
      InitMaskCopy.WellFormed updated.initializationMask ∧
      updated.initializationMask.len = input.entry.allocation.initializationMask.len ∧
      (∀ row ∈ updated.provenanceMap.ptrs, row.1.bytes.toNat+8 ≤ updated.len) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive updated.extra registration.1.protectedTags
        (some query) (some selected) maximum lower width) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin updated.extra query .Write lower (lower+width) ∧
      updated.extra.nodeAt query = some node ∧
      (∀ tag index,input.entry.allocation.extra.indexOfTag tag = some index → updated.extra.indexOfTag tag = some index) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts updated.extra registration.1 ∧
      updated.extra.locations.size = input.entry.allocation.extra.locations.size ∧
      updated.byteSize = input.entry.allocation.byteSize ∧ updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut := by
  dsimp only
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,wildcard] at binding
  obtain ⟨source,_mode,_exposed,_geometry⟩ := binding
  have destination := input.borrow
  rw [source] at destination
  obtain ⟨selectedNone,maximumNone⟩ := S05WildcardEntryBridge.wildcard_metadata _ _ input.selectedRoot input.maximum input.offset 1 runtime.formed destination
  rw [selectedNone,maximumNone] at destination
  obtain ⟨output,operation,_tag,_global,_frame,_readDone,_childDone,post,capacity,growth,roots,
    child,tagged,_rootsEq,⟨positive⟩,_childActivity,_nodeGeometry⟩ :=
    GeneralBorrowRawWildcardFnEntryScopedResources.invoke input.entry.allocation.extra input.tracker.global borrowFrame input.id runtime
      input.offset 1 destination distinct (by omega) (by omega) fresh
  have shape := operation
  simp only [GeneralBorrowRawWildcardFnEntryRuntime.operation,TypedRetagEmpty.allocate_tag input.tracker.global fresh,
    Except.bind,Except.pure,bind,pure] at shape
  have outputEq := Except.ok.inj shape
  subst output
  let registration := GeneralBorrowFnEntryRegistration.registered input.tracker.global borrowFrame input.id fresh
  let read := input.entry.allocation.extra.performBorrowAccessRange .wildcard (Size.ofBytes input.offset) (Size.ofBytes 1)
    .Read registration.1.protectedTags .VisitChildrenOfAccessed
  let tree := (read.tree.newChild (Size.ofBytes input.offset) .wildcard input.tracker.global.nextPointerTag
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes 1) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree
  let current := ReturnProtection.borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry tree
  let next := S04ReturnRetaggedInput.from_borrowed input frames frame borrowFrame fresh tree child (some child)
    (some input.tracker.global.nextPointerTag) tagged capacity positive.base
  have short : tree.nodes.size < 65536 := by
    have nodeGrowth : tree.nodes.size ≤ input.entry.allocation.extra.nodes.size+1 := growth
    omega
  obtain ⟨ctx⟩ := ActualRetagContext.exists_context options remaining span model.preciseOff model.implicitOff
  have retag := S04ReturnWildcardProtection.retag_from_tree options remaining span ctx budget before place input wildcard
    frames frame borrowFrame frameBorrow fresh model.noDataRace read.tree tree rfl _readDone (S04ReturnProtection.child_record _ _childDone)
  obtain ⟨updated,write,extra,bytes,length,mutable,_mask,_maskLen,_pointerBounds,_afterRuntime,_afterTags,_afterPositive,_afterActive⟩ :=
    S04ProtectUninitScopedWrite.from_current (options := options) (remaining := remaining) span current _ next post roots short
      input.tracker.global.nextPointerTag child tagged positive rfl model.noDataRace model.noBackend sync extras outsideSync
  let after := S04ProtectUninit.finished before place input frames frame borrowFrame fresh tree updated
  have configuredWrite : (config options remaining span).retag.writeUninit
      (TypedRetagGeneric.retaggedPlace place input.id input.tracker.global.nextPointerTag) current = .ok () after := by
    rw [ctx.construction]
    change (do
      let access ← ValidityMachine.scopedAccess (config options remaining span).access
      PlaceMachine.writeMemory access (fun _ => false) .uninit
        (TypedRetagGeneric.retaggedPlace place input.id input.tracker.global.nextPointerTag)) current = .ok () after
    have notGhost : (config options remaining span).access.ghostMode = false := by
      rw [(DuplicatePrefixPhysicalContexts.canonical options remaining span).accessEq];rfl
    have scope := S04ProtectUninitWrite.scopedAccess_of_not_ghost (config options remaining span).access current notGhost model.ghostOff
    simp only [bind,EStateM.bind,scope]
    exact write
  have sourceFacts := S02WildcardReturnSameSource.positive input.entry.allocation.extra input.tracker.global borrowFrame input.id runtime
    input.offset destination distinct headroom fresh (some query) (some selected) maximum lower width outside old
  have activity := S02WildcardReturnSameSourceActivity.preserved input.entry.allocation.extra input.tracker.global borrowFrame input.id runtime
    input.offset destination distinct headroom fresh query node present leaf hidden lower (lower+width) active
  have sourcePositive : Nonempty (DuplicatePrefixBorrowAuthorization.Positive updated.extra registration.1.protectedTags
      (some query) (some selected) maximum lower width) := by rw [extra];exact sourceFacts.2.1
  have sourceActivity : GeneralBorrowFreshActiveWithin.ActiveWithin updated.extra query .Write lower (lower+width) := by
    rw [extra];exact activity
  have sourceNode : updated.extra.nodeAt query = some node := by rw [extra];exact sourceFacts.2.2.2.2.1 query node present
  have sourceTags : ∀ tag index,input.entry.allocation.extra.indexOfTag tag = some index → updated.extra.indexOfTag tag = some index := by
    intro tag index found
    rw [extra]
    exact sourceFacts.2.2.2.2.2 tag index found
  have sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts updated.extra registration.1 := by
    rw [extra];exact sourceFacts.2.2.1
  have sourceCapacity : updated.extra.locations.size = input.entry.allocation.extra.locations.size := by
    rw [extra];exact sourceFacts.2.2.2.1
  refine ⟨updated,?_,extra,_mask,_maskLen,_pointerBounds,sourcePositive,sourceActivity,sourceNode,sourceTags,sourceRuntime,sourceCapacity,bytes,length,mutable⟩
  unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,Storage.withCurrent,input.enabled,Option.isSome_some,↓reduceIte]
  erw [retag]
  exact configuredWrite
end
end DuplicatePrefix.S02WildcardReturnSameSourceActivityPacket
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S02WildcardReturnSameSourceActivityPacket." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved same-allocation wildcard source activity packet dependency {dependency}"
