import duplicate_prefix.CurrentCallEmptyConcreteResources
import duplicate_prefix.ConcretePoolArgumentCopy
import duplicate_prefix.ConcreteEmptyRuntimeEntry

/-! Actual live-concrete empty argument copying, specialized to a mapped
physical parent in the Bool allocation. The copied empty source needs no
content family. Presence of the Bool post-resource is derived from the real
copy's deterministic heap installation. -/
namespace DuplicatePrefix.CurrentCallEmptyConcreteCopy
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

/-- One technical view of an already established Bool resource. Appending a
precise row changes no semantic family, loan or active contents. -/
private def viewData (data : Identities) (id : AllocId) (precise : PreciseAllocation) : Identities :=
  {data with interpretation := {data.interpretation with precise := data.interpretation.precise.push (id,precise)}}
theorem copy_same_bool (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
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
    (data : Identities) (owner : Nat) (boolOffset : Nat)
    (B : UniformWindow machine ⟨global,.FnEntry⟩ data owner id boolOffset 1 .ret)
    (allocationEq : B.allocation = entry.allocation)
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
      ∃ technicalData, ∃ Q : UniformWindow
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}
        ⟨(GeneralBorrowFnEntryRegistration.registered global borrowFrame id fresh).1,.FnEntry⟩
        technicalData owner id boolOffset 1 .ret,
        Q.pointer = B.pointer ∧ Q.allocation = entry.allocation.setExtra entryInput.after ∧
        DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra
          (GeneralBorrowFnEntryRegistration.registered global borrowFrame id fresh).1
 := by
  dsimp only
  let entryInput := ConcreteEmptyRuntimeEntry.form entry.allocation.extra global.protectedTags parentTag global.nextPointerTag
    runtime.formed parent parentNode tagged parentAt (ConcreteEmptyRuntimeEntry.counter_fresh _ _ runtime.below) nodeRoom
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 reference).imm
  let postFrame := ConcreteEmptyReferenceArgumentCopy.copiedFrame frame localId value valid
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let afterMachine := (ActualConcretePoolReference.resultState frames postFrame activeMachine borrowFrame global fresh id entry parentTag entryInput).machine
  let post := {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}
  have copied := ConcretePoolArgumentCopy.copy options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id parentTag global base offset nonzero entry frames frame machine localId valid old live cached noClocks ghost shallow cachedAddress
    present borrowFrame frameBorrow enabled fresh entryInput metadata notConstructed view destination
  refine ⟨copied,?_⟩
  have installedPresent : Present (ActualWorld post) id (entry.allocation.setExtra entryInput.after) := by
    simp only [Present,ActualWorld,Array.toList_map]
    apply List.mem_map.mpr
    refine ⟨(id,{entry with allocation := entry.allocation.setExtra entryInput.after}),?_,rfl⟩
    apply Array.mem_toList_iff.mpr
    exact Array.mem_push.mpr (.inr rfl)
  have actualPresent : Present (ActualWorld post) id (B.allocation.setExtra
      (B.allocation.extra.newChild (Size.ofBytes offset) (.concrete parentTag) global.nextPointerTag
        (Miri.DataStructures.DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation) (.ReservedFrz false) true).tree) := by
    rw [allocationEq,show entry.allocation.extra.newChild (Size.ofBytes offset) (.concrete parentTag) global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation) (.ReservedFrz false) true = ⟨entryInput.after,.ok ()⟩ from entryInput.child offset]
    exact installedPresent
  have resource := CurrentCallEmptyConcreteResources.installed B (by simpa only [allocationEq] using runtime)
    parentTag parent parentNode (by simpa only [allocationEq] using tagged) (by simpa only [allocationEq] using parentAt)
    borrowFrame fresh (by simpa only [allocationEq] using nodeRoom) offset post actualPresent
  rw [allocationEq,show entry.allocation.extra.newChild (Size.ofBytes offset) (.concrete parentTag) global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation) (.ReservedFrz false) true = ⟨entryInput.after,.ok ()⟩ from entryInput.child offset] at resource
  obtain ⟨_,nextRuntime,_,child,_,_,parents,binding,issued,window⟩ := resource
  let precise := {B.precise with completion := S05ConcreteProtectedChildCompletion.extend B.precise.completion child parent}
  let technicalData := viewData data id precise
  let Q : UniformWindow post
      ⟨(GeneralBorrowFnEntryRegistration.registered global borrowFrame id fresh).1,.FnEntry⟩ technicalData owner id boolOffset 1 .ret := {
    loan := B.loan,pointer := B.pointer,allocation := entry.allocation.setExtra entryInput.after,precise := precise
    loanAt := B.loanAt,pointerAt := B.pointerAt,pointerId := B.pointerId,present := installedPresent
    preciseAt := Array.mem_toList_iff.mpr (Array.mem_push.mpr (.inr rfl))
    binding := binding,issued := issued,parents := parents,window := window }
  exact ⟨technicalData,Q,rfl,rfl,nextRuntime⟩

end
end DuplicatePrefix.CurrentCallEmptyConcreteCopy
