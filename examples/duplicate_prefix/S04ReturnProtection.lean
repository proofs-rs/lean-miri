import duplicate_prefix.ReturnProtection
import duplicate_prefix.S05ConcreteEntryBridge

namespace DuplicatePrefix.S04ReturnProtection
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Input Miri.Interpreter
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver ReturnProtection
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

theorem retag_bool_window_from_tree
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualRetagContext.Context options remaining span) (budget : Nat)
    (place : MPlaceTy Provenance) (layout : place.layout = RootCompilerFacts.boolLayout)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset : UInt64) (rootTag : BorTag)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id rootTag)) (Size.ofBytes (base + offset)))
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (bounds : offset.toNat + 1 ≤ entry.allocation.byteSize.bytes.toNat)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (race : machine.dataRace = none) (parentTree finalTree : BorrowTree)
    (readTree : (entry.allocation.extra.performBorrowAccessRange (.concrete rootTag) (Size.ofBytes offset)
      (Size.ofBytes 1) .Read (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags
      .VisitChildrenOfAccessed).tree = parentTree)
    (readDone : (entry.allocation.extra.performBorrowAccessRange (.concrete rootTag) (Size.ofBytes offset)
      (Size.ofBytes 1) .Read (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags
      .VisitChildrenOfAccessed).status = .Completed)
    (child : parentTree.newChild (Size.ofBytes offset) (.concrete rootTag) tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes 1) ChildBorrow.fnEntryLocation)
      MachineHooks.protectionPolicy.outsidePermission MachineHooks.protectionPolicy.protector.isSome =
      ⟨finalTree, .ok ()⟩) :
    TypedRetag.retagPlace (config options remaining span).retag budget place MachineHooks.protectionPolicy
      (Storage.withCurrent frames frame machine) =
      .ok (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag)
        (borrowedState frames frame borrowFrame machine tracker fresh id entry finalTree) := by
  have frozen : (config options remaining span).retag.typeIsFreeze place.layout.ty = pure true := by
    rw [layout]
    exact ActualRetagContext.bool_freeze options remaining span ctx
  have allocated : (allocatedMachine machine tracker fresh).borrowTracker = some (allocatedTracker tracker fresh) := rfl
  have reborrow := protected_read_from_fields (config options remaining span).retag ReferenceMetadataFacts.prepared
    (config options remaining span).access (config options remaining span).projection ctx.table ctx.pointers ctx.choice ctx.source
    budget place frames frame borrowFrame (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh)
    allocated frameBorrow id entry base offset 1 rootTag tracker.global.nextPointerTag ChildBorrow.fnEntryLocation
    MachineHooks.protectionPolicy rfl rfl (by decide) frozen rfl
    pointer ctx.resolve ctx.arithmetic cached (by decide)
    (by simpa using bounds) .global ctx.globals ctx.ensure ctx.synchronize present race parentTree finalTree readTree readDone child
  have provenance : place.mplace.ptr.provenance = some (.concrete id rootTag) := by rw [pointer]; rfl
  have result := retag_place_of_reborrow (config options remaining span).retag budget place
    MachineHooks.protectionPolicy (Size.ofBytes 1) Align.ONE (Storage.withCurrent frames frame machine)
    (borrowedState frames frame borrowFrame machine tracker fresh id entry finalTree) tracker enabled fresh id
    (.concrete id rootTag) provenance (ActualRetagContext.bool_size options remaining span ctx place layout) reborrow
  exact result


/-- The destination's one-byte authorization supplies borrowing-entry data;
no initialization of the old bool byte is needed. -/
theorem from_return {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {before : Before} {tracker : MachineHooks.BorrowState}
    {place : MPlaceTy Provenance} {len : UInt64}
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (state : DuplicatePrefixRuntimeInput.OrderedState before tracker)
    (resources : Resources options limits remaining before tracker len)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag) :
    ∃ raw : GeneralBorrowRawFnEntry.Input input.entry.allocation.extra input.tracker.global,
      raw.parentTag = tag ∧ raw.offset = input.offset ∧ raw.len = 1 ∧
      input.source = some raw.parent ∧ input.selectedRoot = some raw.selected ∧
      raw.maximum = input.maximum ∧
      DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global := by
  have same : tracker = input.tracker := Option.some.inj (state.enabled.symm.trans input.enabled)
  subst tracker
  have binding := input.binding
  unfold DuplicatePrefixReferenceInput.Binding at binding
  rw [concrete] at binding
  obtain ⟨idSame,anchor,source,tagged⟩ := binding
  have member : (input.id,input.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some input.live)
  have positive := input.borrow
  rw [source] at positive
  obtain ⟨selected,selectedEq⟩ := S05ConcreteEntryBridge.selected_root _ _ anchor input.selectedRoot input.maximum input.offset 1
    (state.formed (input.id,input.entry) member) positive
  rw [selectedEq] at positive
  have node := resources.nodeRoom (input.id,input.entry) member
  dsimp only at node
  have tags := resources.tagRoom
  let raw : GeneralBorrowRawFnEntry.Input input.entry.allocation.extra input.tracker.global := {
    parentTag := tag, parent := anchor, selected := selected, maximum := input.maximum,
    offset := input.offset, len := 1, tagged := tagged, positive := positive,
    distinct := state.roots (input.id,input.entry) member,
    order := fun _ _ => state.parent_order input.id input.entry input.live,
    short := by omega, nodeRoom := by omega,
    tagRoom := by apply UInt64.lt_iff_toNat_lt.mpr; change input.tracker.global.nextPointerTag.value.toNat < 18446744073709551615; omega }
  exact ⟨raw,rfl,rfl,rfl,source,selectedEq,rfl,
    ⟨state.formed _ member,state.coherent _ member,state.possible _ member,resources.tagsBelow _ member⟩⟩

theorem child_record (result : BorrowTree.ChildInsertResult) (done : result.outcome = .ok ()) :
    result = ⟨result.tree,.ok ()⟩ := by
  cases result with
  | mk tree outcome => simp only at done; cases done; rfl

/-- Real protected return-slot retag, for a concrete destination in a general
allocation/tree and at any valid byte offset. The old byte is not read. -/
theorem invoke_concrete
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (budget : Nat)
    (before : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (len : UInt64)
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (state : DuplicatePrefixRuntimeInput.OrderedState before tracker)
    (resources : Resources options limits remaining before tracker len)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame) :
    ∃ (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
      (finalTree : BorrowTree),
      TypedRetag.retagPlace (config options remaining span).retag budget place MachineHooks.protectionPolicy
        (Storage.withCurrent frames frame before) =
        .ok (TypedRetagGeneric.retaggedPlace place input.id input.tracker.global.nextPointerTag)
          (borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry finalTree) ∧
      ∃ child selected,
        input.selectedRoot = some selected ∧
        finalTree.indexOfTag input.tracker.global.nextPointerTag = some child ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive finalTree
          (registeredGlobal (allocatedTracker input.tracker fresh) input.tracker.global.nextPointerTag).protectedTags
          (some child) (some selected) input.maximum input.offset 1) := by
  obtain ⟨ctx⟩ := ActualRetagContext.exists_context options remaining span model.preciseOff model.implicitOff
  obtain ⟨raw,parentTag,offset,length,source,selected,maximum,runtime⟩ := from_return input state resources tag concrete
  obtain ⟨output,actual,outputTag,global,frameEq,readDone,childDone,afterRuntime,capacity,growth,
    child,lookup,roots,⟨positive⟩,activity⟩ :=
    GeneralBorrowRawFnEntry.invoke_positive input.entry.allocation.extra input.tracker.global borrowFrame input.id runtime raw
  have shape := actual
  simp only [GeneralBorrowForestFnEntry.operation,TypedRetagEmpty.allocate_tag input.tracker.global raw.tagRoom,
    Except.bind,Except.pure,bind,pure] at shape
  have outputEq := Except.ok.inj shape
  subst output
  have pointer : place.mplace.ptr = Pointer.new (some (.concrete input.id tag)) (Size.ofBytes (input.base+input.offset)) := by
    have addr := input.pointerAddress
    have ptrEq : input.pointer = Pointer.new (.concrete input.id tag) (Size.ofBytes (input.base+input.offset)) := by
      cases h : input.pointer with
      | mk off prov =>
        cases off with
        | mk bytes =>
          simp only [h,Pointer.provenance] at concrete
          simp only [h,Pointer.offset,Size.bytes] at addr
          cases concrete
          cases addr
          rfl
    rw [input.physicalPointer,ptrEq]
    rfl
  let accessed := GeneralBorrowForestProtected.read input.entry.allocation.extra
    (GeneralBorrowFnEntryRegistration.registered input.tracker.global borrowFrame input.id raw.tagRoom).1.protectedTags
    raw.parentTag raw.offset raw.len .VisitChildrenOfAccessed
  let final := accessed.tree.newChild (Size.ofBytes raw.offset) (.concrete raw.parentTag)
    input.tracker.global.nextPointerTag (DedupRangeMap.new (Size.ofBytes raw.len) GeneralBorrowFreshChild.inside)
    (.ReservedFrz false) true
  refine ⟨raw.tagRoom,final.tree,?_,child,raw.selected,selected,?_,?_⟩
  · apply retag_bool_window_from_tree options remaining span ctx budget place input.layout frames frame borrowFrame
      before input.tracker input.enabled frameBorrow raw.tagRoom input.id input.entry input.base input.offset tag pointer
      input.cachedBase (by simpa only [input.size,Size.ofBytes] using input.bounds) input.live model.noDataRace accessed.tree final.tree
    · simp only [final,accessed,parentTag,offset,length,maximum,GeneralBorrowForestProtected.read,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,MachineHooks.protectionPolicy,Option.isSome]
    · simpa only [final,accessed,parentTag,offset,length,maximum,GeneralBorrowForestProtected.read,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,MachineHooks.protectionPolicy,Option.isSome] using readDone
    · have eq := child_record _ childDone
      simpa only [final,accessed,parentTag,offset,length,maximum,GeneralBorrowForestProtected.read,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,MachineHooks.protectionPolicy,Option.isSome] using eq
  · simpa only [final,accessed,parentTag,offset,length,maximum,GeneralBorrowForestProtected.read,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,MachineHooks.protectionPolicy,Option.isSome] using lookup
  · simpa only [final,accessed,parentTag,offset,length,maximum,GeneralBorrowForestProtected.read,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,MachineHooks.protectionPolicy,Option.isSome] using (show Nonempty _ from ⟨positive⟩)

end
end DuplicatePrefix.S04ReturnProtection
