import duplicate_prefix.CurrentCallEmptyConcreteResources
import duplicate_prefix.ConcretePoolArgumentCopy
import duplicate_prefix.ConcreteEmptyRuntimeEntry
import duplicate_prefix.WildcardPoolHitArgumentCopy

/-! Actual empty-source tree installation at a different allocation preserves
the original Bool row. Fresh registration observes the old Bool nodes equally;
no source contents or grant are needed. -/
namespace DuplicatePrefix.CurrentCallEmptyOtherBool
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Presence is reconstructed from the actual filtered/pushed heap, not
assumed for a hypothetical pre-state with a changed tree. -/
theorem after_install {before : Before} {tracker : MachineHooks.BorrowState} {data : Identities}
    {owner : Nat} {id : AllocId} {offset : Nat}
    (B : UniformWindow before tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (frame : FrameState) (sourceId : AllocId) (different : sourceId ≠ id)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tree : BorrowTree)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (post : Before) (memoryEq : post.memory = RetagEntry.updatedMemory before.memory sourceId entry tree) :
    ∃ Q : UniformWindow post
        {tracker with global := (GeneralBorrowFnEntryRegistration.registered tracker.global frame sourceId room).1}
        data owner id offset 1 .ret,
      Q.pointer = B.pointer ∧ Q.allocation = B.allocation ∧ Q.precise = B.precise ∧
      DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra
        (GeneralBorrowFnEntryRegistration.registered tracker.global frame sourceId room).1 := by
  have present : Present (ActualWorld post) id B.allocation := by
    have old := B.present
    simp only [Present,ActualWorld,Array.toList_map] at old ⊢
    obtain ⟨⟨actualId,oldEntry⟩,member,equal⟩ := List.mem_map.mp old
    have idEq : actualId = id := (Prod.mk.inj equal).1
    subst actualId
    have allocationEq : oldEntry.allocation = B.allocation := (Prod.mk.inj equal).2
    apply List.mem_map.mpr
    refine ⟨(id,oldEntry),?_,by simp only [allocationEq]⟩
    rw [memoryEq]
    apply Array.mem_toList_iff.mpr
    apply Array.mem_push.mpr
    apply Or.inl
    exact Array.mem_filter.mpr ⟨Array.mem_toList_iff.mp member,by simp [Ne.symm different]⟩
  let next := {tracker with global := (GeneralBorrowFnEntryRegistration.registered tracker.global frame sourceId room).1}
  have issued := CurrentCallAllocationLicense.spatial B.issued post next B.allocation present
    (by rfl) rfl rfl rfl (by intro position root slot;exact slot)
    (by intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩)
    B.precise.completion (by intro root origin edge;exact edge)
  let Q : UniformWindow post next data owner id offset 1 .ret := {
    loan := B.loan,pointer := B.pointer,allocation := B.allocation,precise := B.precise
    loanAt := B.loanAt,pointerAt := B.pointerAt,pointerId := B.pointerId
    present := present,issued := issued,preciseAt := B.preciseAt,binding := B.binding,parents := B.parents
    window := by
      intro byte inside
      obtain ⟨bound,owned⟩ := B.window byte inside
      exact ⟨bound,CurrentCallEmptyConcreteResources.registered_embeds B.allocation tracker.global runtime frame sourceId room
        B.precise.completion B.pointer.grant byte.2 _ owned⟩ }
  exact ⟨Q,rfl,rfl,rfl,(GeneralBorrowFnEntryRegistrationRuntime.prepare B.allocation.extra tracker.global frame sourceId room runtime).2.2.2.1⟩

private def sourceSlot (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (room : tree.nodes.size+1 ≤ 4294967295) : WildcardHitPoolRoot.Slot tree := by
  have accounting := runtime.formed.allocator.accounting
  have fits : tree.tagMapping.mapping.size ≤ 4294967295 := by
    unfold GeneralBorrowFreshStagePool.Accounting at accounting
    omega
  exact WildcardHitPoolRoot.factory tree runtime.formed.allocator.pool accounting fits

theorem concrete (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (validationEq : options.limits.validation = validityFuel + 1)
    (id : AllocId) (parentTag : BorTag) (global : GlobalState)
    (base offset : UInt64) (nonzero : base+offset ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (valid : localId < frame.locals.size)
    (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some reference)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global, .FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra global)
    (parent : UniIndex) (parentNode : TreeNode)
    (tagged : entry.allocation.extra.indexOfTag parentTag = some parent)
    (parentAt : entry.allocation.extra.nodeAt parent = some parentNode)
    (nodeRoom : entry.allocation.extra.nodes.size+1 ≤ 4294967295)
    (data : Identities) (owner : Nat) (boolId : AllocId) (boolOffset : Nat)
    (B : UniformWindow machine ⟨global,.FnEntry⟩ data owner boolId boolOffset 1 .ret)
    (boolRuntime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra global)
    (different : id ≠ boolId)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any
      (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId reference) :
    let entryInput := ConcreteEmptyRuntimeEntry.form entry.allocation.extra global.protectedTags parentTag global.nextPointerTag
      runtime.formed parent parentNode tagged parentAt (ConcreteEmptyRuntimeEntry.counter_fresh _ _ runtime.below) nodeRoom
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 reference).imm
    let postFrame := ConcreteEmptyReferenceArgumentCopy.copiedFrame frame localId value valid
    let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
    let afterFrame := TypedBorrowSteps.registeredFrame postFrame borrowFrame id global.nextPointerTag
    let afterMachine := (ActualConcretePoolReference.resultState frames postFrame activeMachine borrowFrame global fresh id entry parentTag entryInput).machine
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyAllowTransmute ()
      ⟨.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 reference).imm, reference⟩ view (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {afterFrame with locals := (afterFrame.locals.set localId
          {value := .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base+offset))) 0 reference).imm),
           layout := (afterFrame.locals[localId]'(by simpa [afterFrame,postFrame,ConcreteEmptyReferenceArgumentCopy.copiedFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow] using valid)).layout}
          (by simpa [afterFrame,postFrame,ConcreteEmptyReferenceArgumentCopy.copiedFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow] using valid))}
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}) ∧
      ∃ Q : UniformWindow
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}
        ⟨(GeneralBorrowFnEntryRegistration.registered global borrowFrame id fresh).1,.FnEntry⟩
        data owner boolId boolOffset 1 .ret,
        Q.pointer = B.pointer ∧ Q.allocation = B.allocation ∧ Q.precise = B.precise ∧
        DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra
          (GeneralBorrowFnEntryRegistration.registered global borrowFrame id fresh).1
 := by
  dsimp only
  let entryInput := ConcreteEmptyRuntimeEntry.form entry.allocation.extra global.protectedTags parentTag global.nextPointerTag
    runtime.formed parent parentNode tagged parentAt (ConcreteEmptyRuntimeEntry.counter_fresh _ _ runtime.below) nodeRoom
  refine ⟨ConcretePoolArgumentCopy.copy options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id parentTag global base offset nonzero entry frames frame machine localId valid old live cached noClocks ghost shallow cachedAddress present
    borrowFrame frameBorrow enabled fresh entryInput metadata notConstructed view destination,?_⟩
  exact after_install B boolRuntime borrowFrame id different entry entryInput.after fresh _ rfl


theorem wildcard (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (validationEq : options.limits.validation = validityFuel + 1)
    (id : AllocId) (global : GlobalState)
    (base offset : UInt64) (nonzero : base+offset ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (valid : localId < frame.locals.size)
    (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some reference)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global, .FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (inverse : WildcardGeneralHitReborrow.Geometry machine.user.addresses.intToPtrMap (base+offset) base id entry.allocation.byteSize)
    (exposed : machine.user.addresses.exposed.contains id = true)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra global)
    (nodeRoom : entry.allocation.extra.nodes.size+1 ≤ 4294967295)
    (data : Identities) (owner : Nat) (boolId : AllocId) (boolOffset : Nat)
    (B : UniformWindow machine ⟨global,.FnEntry⟩ data owner boolId boolOffset 1 .ret)
    (boolRuntime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra global)
    (different : id ≠ boolId)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any
      (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId reference) :
    let rootSlot := sourceSlot entry.allocation.extra global runtime nodeRoom
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 reference).imm
    let postFrame := ConcreteEmptyReferenceArgumentCopy.copiedFrame frame localId value valid
    let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
    let afterFrame := TypedBorrowSteps.registeredFrame postFrame borrowFrame id global.nextPointerTag
    let afterMachine := (ActualWildcardPoolHitReference.resultState frames postFrame activeMachine borrowFrame global fresh id entry rootSlot).machine
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyAllowTransmute ()
      ⟨.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 reference).imm, reference⟩ view (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {afterFrame with locals := (afterFrame.locals.set localId
          {value := .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base+offset))) 0 reference).imm),
           layout := (afterFrame.locals[localId]'(by simpa [afterFrame,postFrame,ConcreteEmptyReferenceArgumentCopy.copiedFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow] using valid)).layout}
          (by simpa [afterFrame,postFrame,ConcreteEmptyReferenceArgumentCopy.copiedFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow] using valid))}
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}) ∧
      ∃ Q : UniformWindow
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}
        ⟨(GeneralBorrowFnEntryRegistration.registered global borrowFrame id fresh).1,.FnEntry⟩
        data owner boolId boolOffset 1 .ret,
        Q.pointer = B.pointer ∧ Q.allocation = B.allocation ∧ Q.precise = B.precise ∧
        DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra
          (GeneralBorrowFnEntryRegistration.registered global borrowFrame id fresh).1
 := by
  dsimp only
  let rootSlot := sourceSlot entry.allocation.extra global runtime nodeRoom
  have tagMapFresh := ConcreteEmptyRuntimeEntry.counter_fresh _ _ runtime.below
  refine ⟨WildcardPoolHitArgumentCopy.copy options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id global base offset nonzero entry frames frame machine localId valid old live cached noClocks ghost shallow cachedAddress present
    borrowFrame frameBorrow enabled fresh addressMode inverse exposed tagMapFresh rootSlot metadata notConstructed view destination,?_⟩
  exact after_install B boolRuntime borrowFrame id different entry (rootSlot.after global.nextPointerTag) fresh _ rfl

end
end DuplicatePrefix.CurrentCallEmptyOtherBool
