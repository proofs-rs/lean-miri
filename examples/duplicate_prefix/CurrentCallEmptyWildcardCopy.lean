import duplicate_prefix.CurrentCallResourceZeroRoot
import duplicate_prefix.CurrentCallEmptyConcreteResources
import duplicate_prefix.WildcardPoolHitArgumentCopy

/-! An actual live wildcard empty argument creates an unassigned dormant root.
The Bool resource is retained in that actual copy's installed allocation; no
source family, exposed-origin choice, or empty-source contents are required. -/
namespace DuplicatePrefix.CurrentCallEmptyWildcardCopy
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

private def slot (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (room : tree.nodes.size+1 ≤ 4294967295) : WildcardHitPoolRoot.Slot tree := by
  have accounting := runtime.formed.allocator.accounting
  have fits : tree.tagMapping.mapping.size ≤ 4294967295 := by
    unfold GeneralBorrowFreshStagePool.Accounting at accounting
    omega
  exact WildcardHitPoolRoot.factory tree runtime.formed.allocator.pool accounting fits

private def viewData (data : Identities) (id : AllocId) (precise : PreciseAllocation) : Identities :=
  {data with interpretation := {data.interpretation with precise := data.interpretation.precise.push (id,precise)}}
theorem copy_same_bool (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
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
    (data : Identities) (owner : Nat) (boolOffset : Nat)
    (B : UniformWindow machine ⟨global,.FnEntry⟩ data owner id boolOffset 1 .ret)
    (allocationEq : B.allocation = entry.allocation)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any
      (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId reference) :
    let rootSlot := slot entry.allocation.extra global runtime nodeRoom
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
      ∃ technicalData, ∃ Q : UniformWindow
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}
        ⟨(GeneralBorrowFnEntryRegistration.registered global borrowFrame id fresh).1,.FnEntry⟩
        technicalData owner id boolOffset 1 .ret,
        Q.pointer = B.pointer ∧ Q.allocation = entry.allocation.setExtra (rootSlot.after global.nextPointerTag) ∧
        Q.precise.completion = CurrentCallResourceZeroRoot.unassigned B.precise.completion rootSlot.index ∧
        Q.precise.completion.parents[rootSlot.index.toNat]? = some none ∧
        DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra
          (GeneralBorrowFnEntryRegistration.registered global borrowFrame id fresh).1
 := by
  dsimp only
  let rootSlot := slot entry.allocation.extra global runtime nodeRoom
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 reference).imm
  let postFrame := ConcreteEmptyReferenceArgumentCopy.copiedFrame frame localId value valid
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let afterMachine := (ActualWildcardPoolHitReference.resultState frames postFrame activeMachine borrowFrame global fresh id entry rootSlot).machine
  let post := {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}
  let registered := GeneralBorrowFnEntryRegistration.registered global borrowFrame id fresh
  let next : MachineHooks.BorrowState := ⟨registered.1,.FnEntry⟩
  obtain ⟨_,held,_,advanced,_,tagFresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare entry.allocation.extra global borrowFrame id fresh runtime
  have copied := WildcardPoolHitArgumentCopy.copy options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id global base offset nonzero entry frames frame machine localId valid old live cached noClocks ghost shallow cachedAddress present
    borrowFrame frameBorrow enabled fresh addressMode inverse exposed tagFresh rootSlot metadata notConstructed view destination
  refine ⟨copied,?_⟩
  have presentAfter : Present (ActualWorld post) id (entry.allocation.setExtra (rootSlot.after global.nextPointerTag)) := by
    simp only [Present,ActualWorld,Array.toList_map]
    apply List.mem_map.mpr
    refine ⟨(id,{entry with allocation := entry.allocation.setExtra (rootSlot.after global.nextPointerTag)}),?_,rfl⟩
    apply Array.mem_toList_iff.mpr
    exact Array.mem_push.mpr (.inr rfl)
  have model : ParentInterpretation entry.allocation.extra B.precise.completion := by simpa only [allocationEq] using B.parents
  have tagBound : global.nextPointerTag.value.toNat < registered.1.nextPointerTag.value.toNat := by
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag fresh).value.toNat
    rw [GenericFunctionEntryNumerics.successor_value];omega
  have heldBool : registered.1.protectedTags.contains global.nextPointerTag = true := by
    simp only [ProtectedTags.contains,registered,held,Option.isSome_some]
  obtain ⟨root,rootAt,_,_,_⟩ := B.issued.capability.rootNode
  have primary : ∃ node,entry.allocation.extra.nodes.get allocationRoot=some node := by
    exact ⟨root,by simpa only [allocationEq] using rootAt⟩
  have built := CurrentCallResourceZeroRoot.construct entry.allocation registered.1 B.precise.completion advanced model primary
    rootSlot global.nextPointerTag tagFresh nodeRoom tagBound heldBool offset
  obtain ⟨_,current,parents,parentNone,_,_,_,embedding⟩ := built
  have old : ∀ index node,entry.allocation.extra.nodes.get index=some node →
      ∃ changed,(rootSlot.after global.nextPointerTag).nodes.get index=some changed ∧ changed.tag=node.tag ∧
        changed.parent=node.parent ∧ changed.isExposed=node.isExposed ∧ changed.defaultInitialPermission=node.defaultInitialPermission := by
    intro index node found
    exact ⟨node,CurrentCallResourceZeroRoot.old_nodes entry.allocation.extra rootSlot global.nextPointerTag index node found,rfl,rfl,rfl,rfl⟩
  have oldIssued : SpatialDelegation machine ⟨global,.FnEntry⟩ id entry.allocation B.precise.completion B.pointer.grant := by
    simpa only [allocationEq] using B.issued
  have issued := CurrentCallAllocationLicense.spatial oldIssued post next
    (entry.allocation.setExtra (rootSlot.after global.nextPointerTag)) presentAfter (by rfl) rfl rfl rfl
    (CurrentCallResourceZeroRoot.old_root entry.allocation.extra rootSlot global.nextPointerTag) old
    (CurrentCallResourceZeroRoot.unassigned B.precise.completion rootSlot.index)
    (by intro root origin edge;exact (CurrentCallResourceZeroRoot.edge_iff _ _ _ _).mpr edge)
  have binding : PointerBinds (entry.allocation.setExtra (rootSlot.after global.nextPointerTag)) B.pointer := by
    obtain ⟨node,nodeAt,_,original⟩ := B.binding
    have oldAt : entry.allocation.extra.nodes.get B.pointer.grant=some node := by simpa only [allocationEq] using nodeAt
    have nextAt := CurrentCallResourceZeroRoot.old_nodes entry.allocation.extra rootSlot global.nextPointerTag B.pointer.grant node oldAt
    exact ⟨node,nextAt,current.formed.allocator.nodeTags B.pointer.grant node nextAt,original⟩
  let precise := {B.precise with completion := CurrentCallResourceZeroRoot.unassigned B.precise.completion rootSlot.index}
  let technicalData := viewData data id precise
  let Q : UniformWindow post next technicalData owner id boolOffset 1 .ret := {
    loan := B.loan,pointer := B.pointer,allocation := entry.allocation.setExtra (rootSlot.after global.nextPointerTag),precise := precise
    loanAt := B.loanAt,pointerAt := B.pointerAt,pointerId := B.pointerId,present := presentAfter
    preciseAt := Array.mem_toList_iff.mpr (Array.mem_push.mpr (.inr rfl))
    binding := binding,issued := issued,parents := parents
    window := by
      intro byte inside
      obtain ⟨bound,owned⟩ := B.window byte inside
      refine ⟨by change byte.2 < entry.allocation.len;simpa only [allocationEq] using bound,?_⟩
      obtain ⟨node,nodeAt,_,_⟩ := B.binding
      have oldAt : entry.allocation.extra.nodes.get B.pointer.grant=some node := by simpa only [allocationEq] using nodeAt
      have registeredOwned := CurrentCallEmptyConcreteResources.registered_embeds B.allocation global
        (by simpa only [allocationEq] using runtime) borrowFrame id fresh B.precise.completion B.pointer.grant byte.2 _ owned
      exact embedding B.pointer.grant node oldAt byte.2 _ (by simpa only [allocationEq] using registeredOwned) }
  exact ⟨technicalData,Q,rfl,rfl,rfl,parentNone,current⟩

end
end DuplicatePrefix.CurrentCallEmptyWildcardCopy
