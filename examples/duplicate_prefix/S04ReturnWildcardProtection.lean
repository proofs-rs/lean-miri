import duplicate_prefix.S04ReturnProtection
import duplicate_prefix.S04ReturnPointerBridge
import duplicate_prefix.S05WildcardEntryBridge

namespace DuplicatePrefix.S04ReturnWildcardProtection
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Input Miri.Interpreter
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver ReturnProtection
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Raw wildcard destination metadata and runtime/headroom, independent of
initialization of the destination's old byte. -/
theorem from_return {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {before : Before} {tracker : MachineHooks.BorrowState}
    {place : MPlaceTy Provenance} {len : UInt64}
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (resources : Resources options limits remaining before tracker len)
    (wildcard : input.pointer.provenance = .wildcard) :
    input.source = none ∧ input.selectedRoot = none ∧ input.maximum = none ∧
      DuplicatePrefixBorrowAuthorization.Positive input.entry.allocation.extra input.tracker.global.protectedTags
        none none none input.offset 1 ∧
      DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global ∧
      input.entry.allocation.extra.roots.toList.Nodup ∧
      input.entry.allocation.extra.nodes.size < 65536 ∧
      input.entry.allocation.extra.nodes.size+1 ≤ 4294967295 ∧
      input.tracker.global.nextPointerTag.value < 18446744073709551615 := by
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,wildcard] at binding
  obtain ⟨source,mode,exposed,geometry⟩ := binding
  have same : tracker = input.tracker := Option.some.inj (state.enabled.symm.trans input.enabled)
  subst tracker
  have member : (input.id,input.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some input.live)
  have positive := input.borrow
  rw [source] at positive
  obtain ⟨selected,maximum⟩ := S05WildcardEntryBridge.wildcard_metadata _ _ input.selectedRoot input.maximum input.offset 1
    (state.formed _ member) positive
  rw [selected,maximum] at positive
  have nodes := resources.nodeRoom (input.id,input.entry) member
  dsimp only at nodes
  have tags := resources.tagRoom
  refine ⟨source,selected,maximum,positive,⟨state.formed _ member,state.coherent _ member,state.possible _ member,resources.tagsBelow _ member⟩,
    state.roots _ member,by omega,by omega,?_⟩
  apply UInt64.lt_iff_toNat_lt.mpr
  change input.tracker.global.nextPointerTag.value.toNat < 18446744073709551615
  omega

/-- Exact actual bool-slot protection retag for wildcard provenance, from
raw initial authorization and tree operation certificates. -/
theorem retag_from_tree
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualRetagContext.Context options remaining span) (budget : Nat)
    (before : Before) (place : MPlaceTy Provenance)
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (wildcard : input.pointer.provenance = .wildcard)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (race : before.dataRace = none) (parentTree finalTree : BorrowTree)
    (readTree : (input.entry.allocation.extra.performBorrowAccessRange .wildcard (Size.ofBytes input.offset)
      (Size.ofBytes 1) .Read (registeredGlobal (allocatedTracker input.tracker fresh) input.tracker.global.nextPointerTag).protectedTags
      .VisitChildrenOfAccessed).tree = parentTree)
    (readDone : (input.entry.allocation.extra.performBorrowAccessRange .wildcard (Size.ofBytes input.offset)
      (Size.ofBytes 1) .Read (registeredGlobal (allocatedTracker input.tracker fresh) input.tracker.global.nextPointerTag).protectedTags
      .VisitChildrenOfAccessed).status = .Completed)
    (child : parentTree.newChild (Size.ofBytes input.offset) .wildcard input.tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes 1) ChildBorrow.fnEntryLocation)
      MachineHooks.protectionPolicy.outsidePermission MachineHooks.protectionPolicy.protector.isSome =
      ⟨finalTree,.ok ()⟩) :
    TypedRetag.retagPlace (config options remaining span).retag budget place MachineHooks.protectionPolicy
      (Storage.withCurrent frames frame before) =
      .ok (TypedRetagGeneric.retaggedPlace place input.id input.tracker.global.nextPointerTag)
        (borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry finalTree) := by
  let h := (config options remaining span).retag
  let start := Storage.withCurrent frames frame (allocatedMachine before input.tracker fresh)
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,wildcard] at binding
  obtain ⟨source,mode,exposed,geometry⟩ := binding
  rw [input.pointerAddress] at geometry
  have pointer : place.mplace.ptr = Pointer.new (some .wildcard) (Size.ofBytes (input.base+input.offset)) := by
    rw [input.physicalPointer]
    have offset : input.pointer.offset = Size.ofBytes (input.base+input.offset) := by
      change Size.ofBytes input.pointer.offset.bytes = _
      exact congrArg Size.ofBytes input.pointerAddress
    simp only [Pointer.withOptionalProvenance,Pointer.new,offset,wildcard]
  have frozen : h.typeIsFreeze place.layout.ty = pure true := by
    rw [input.layout]
    exact ActualRetagContext.bool_freeze options remaining span ctx
  have check : h.checkPtrAccess place.mplace.ptr (Size.ofBytes (1 : UInt64)) start = .ok () start := by
    rw [ctx.source.check,pointer]
    apply GeneralBorrowPositiveWildcardWindowPointerChecks.check ctx.pointers _ start input.base input.offset (1 : UInt64) input.id input.entry geometry ctx.resolve ctx.arithmetic mode exposed input.cachedBase input.live
    · exact UInt64.lt_iff_toNat_lt.mpr (by decide : 0 < (1 : UInt64).toNat)
    · decide
    · simpa [input.size,Size.ofBytes] using input.bounds
  have resolve : h.resolveAllocation place.mplace.ptr start = .ok (some ⟨input.id,Size.ofBytes input.offset,.wildcard⟩) start := by
    rw [ctx.source.resolve,pointer]
    have resolved := WildcardGeneralHitReborrow.resolve ctx.pointers start (input.base+input.offset) input.base input.id input.entry geometry ctx.arithmetic mode exposed input.cachedBase input.live
    simpa only [UInt64.add_comm input.base input.offset,UInt64.add_sub_cancel] using resolved
  have inside := TypedRetagPolicyFields.inside_for_policy h budget place (Size.ofBytes 1) MachineHooks.protectionPolicy ChildBorrow.fnEntryLocation rfl ctx.source.precise frozen
  have reborrow := protected_reborrow_of_steps h budget place frames frame borrowFrame
    (allocatedMachine before input.tracker fresh) (allocatedTracker input.tracker fresh) rfl frameBorrow
    input.id input.entry input.offset 1 .wildcard input.tracker.global.nextPointerTag ChildBorrow.fnEntryLocation
    MachineHooks.protectionPolicy rfl rfl (by decide) check resolve (by rw [ctx.source.log]) inside
    .global ctx.globals (Eq.trans ctx.source.ensure ctx.ensure) ctx.synchronize input.live race parentTree finalTree readTree readDone child
  have provenance : place.mplace.ptr.provenance = some .wildcard := by rw [pointer];rfl
  exact retag_place_of_reborrow h budget place MachineHooks.protectionPolicy (Size.ofBytes 1) Align.ONE
    (Storage.withCurrent frames frame before) (borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry finalTree)
    input.tracker input.enabled fresh input.id .wildcard provenance
    (ActualRetagContext.bool_size options remaining span ctx place input.layout) reborrow

/-- Wildcard destination protection completes with a real fresh concrete
child and one-byte Positive, without successful-operation premises. -/
theorem invoke_wildcard
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (budget : Nat) (before : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (len : UInt64)
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (resources : Resources options limits remaining before tracker len)
    (wildcard : input.pointer.provenance = .wildcard)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame) :
    ∃ (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
      (finalTree : BorrowTree),
      TypedRetag.retagPlace (config options remaining span).retag budget place MachineHooks.protectionPolicy
        (Storage.withCurrent frames frame before) =
        .ok (TypedRetagGeneric.retaggedPlace place input.id input.tracker.global.nextPointerTag)
          (borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry finalTree) ∧
      ∃ child,finalTree.indexOfTag input.tracker.global.nextPointerTag = some child ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive finalTree
          (registeredGlobal (allocatedTracker input.tracker fresh) input.tracker.global.nextPointerTag).protectedTags
          (some child) (some child) (some input.tracker.global.nextPointerTag) input.offset 1) := by
  obtain ⟨ctx⟩ := ActualRetagContext.exists_context options remaining span model.preciseOff model.implicitOff
  obtain ⟨source,selected,maximum,positive,runtime,distinct,short,nodes,tags⟩ := from_return input state resources wildcard
  obtain ⟨output,actual,outputTag,global,frameEq,readDone,childDone,afterRuntime,capacity,growth,
    child,lookup,roots,capability,activity,geometry⟩ :=
    GeneralBorrowRawWildcardFnEntryResources.invoke input.entry.allocation.extra input.tracker.global
      borrowFrame input.id runtime input.offset 1 positive distinct short nodes tags
  have shape := actual
  simp only [GeneralBorrowRawWildcardFnEntryRuntime.operation,TypedRetagEmpty.allocate_tag input.tracker.global tags,
    Except.bind,Except.pure,bind,pure] at shape
  have outputEq := Except.ok.inj shape
  subst output
  let accessed := input.entry.allocation.extra.performBorrowAccessRange .wildcard (Size.ofBytes input.offset)
    (Size.ofBytes 1) .Read
    (GeneralBorrowFnEntryRegistration.registered input.tracker.global borrowFrame input.id tags).1.protectedTags
    .VisitChildrenOfAccessed
  let final := accessed.tree.newChild (Size.ofBytes input.offset) .wildcard input.tracker.global.nextPointerTag
    (DedupRangeMap.new (Size.ofBytes 1) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
  refine ⟨tags,final.tree,?_,child,?_,?_⟩
  · apply retag_from_tree options remaining span ctx budget before place input wildcard frames frame borrowFrame
      frameBorrow tags model.noDataRace accessed.tree final.tree
    · simp only [accessed,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker]
    · simpa only [GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker] using readDone
    · have eq := S04ReturnProtection.child_record _ childDone
      simpa only [final,accessed,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,MachineHooks.protectionPolicy,Option.isSome] using eq
  · simpa only [final,accessed,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector] using lookup
  · simpa only [final,accessed,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker] using capability

end
end DuplicatePrefix.S04ReturnWildcardProtection
