import duplicate_prefix.CurrentCallSpatialEntryConstructor
import duplicate_prefix.CurrentCallTypedSourceCopy

/-! One C-free spatial source role drives the actual whole-span typed FnEntry
and scoped argument copy. Proof cells do not split the interpreter operation.
Post-world cover installation is separate from these actual returned facts. -/
namespace DuplicatePrefix.CurrentCallSpatialTypedSourceCopy
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallSpatialCover CurrentCallResourceNormalization GeneralRangeMapOrigins
open GeneralBorrowFnEntryRegistration TypedBorrowSteps ReferenceBorrowDriver
open CanonicalConfigFacts ActualReferenceContext CurrentCallTypedFnEntry CurrentCallTypedSourceCopy
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Current RoleCover plus physical and fixed-metadata inputs supply the SAME
actual Read, constructor, typed validation/copy, and restored retag mode. No
operation status or uniform completion is supplied by the caller. -/
theorem invoke (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (cover : CurrentCallSpatialCover.Context before)
    (offset : Nat) (len : UInt64) (role : RoleCover before tracker cover .mut offset len.toNat)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (worldIds : ((ActualWorld before).toList.map Prod.fst).Nodup)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (enabled : before.borrowTracker=some tracker)
    (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (binding : CandidateCallBindings.WindowBinding before role.family.value role.backing.id offset len.toNat)
    (positive : 0<len.toNat) (signedFits : len.toNat<9223372036854775808)
    (room : tracker.global.nextPointerTag.value<18446744073709551615) (race : before.dataRace=none)
    (nullComparator : ProjectionMetadataFacts.NullComparator) (dynamicFuel validationFuel : Nat)
    (fuelEq : options.place.dynamicFuel=dynamicFuel+1) (validationEq : options.limits.validation=validationFuel+1)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)).metadata=PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)))
    (debugOff : options.place.debugAssertions=false) (ghostOff : before.user.payload.ghost=false)
    (shallowMode : before.user.payload.validation=.Shallow)
    (localId : MIR.LocalId) (valid : localId<frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[localId].value=.live (.immediate old))
    (cached : frame.locals[localId].layout=some ActualReferenceMetadata.reference) (noClocks : frame.extra.dataRace=none) :
    let output := CurrentCallSpatialEntryRead.output role borrowFrame room (UInt64.ofNat offset) len
    ∃ (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (child : UniIndex),
      before.memory.live.find? (fun row=>row.1==role.backing.id)=some (role.backing.id,entry) ∧
      entry.allocation=role.backing.allocation ∧
      CandidateCurrentFnEntryRaw.operation entry.allocation.extra tracker.global borrowFrame role.backing.id
        role.family.value.provenance (UInt64.ofNat offset) len=.ok output ∧
      output.tag=tracker.global.nextPointerTag ∧
      output.global=(registered tracker.global borrowFrame role.backing.id room).1 ∧
      output.frame=(registered tracker.global borrowFrame role.backing.id room).2 ∧
      output.child.tree.indexOfTag output.tag=some child ∧
      output.access.status=.Completed ∧ output.child.outcome=.ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      output.child.tree.locations.size=role.backing.allocation.extra.locations.size ∧
      output.child.tree.nodes.size≤role.backing.allocation.extra.nodes.size+1 ∧
      (∀ (position : Nat) (root : UniIndex),role.backing.allocation.extra.roots[position]?=some root → output.child.tree.roots[position]?=some root) ∧
      (∀ index node,role.backing.allocation.extra.nodes.get index=some node →
        ∃ next,output.child.tree.nodes.get index=some next ∧ next.tag=node.tag ∧ next.parent=node.parent ∧
          next.isExposed=node.isExposed ∧ next.defaultInitialPermission=node.defaultInitialPermission) ∧
      (∃node,output.child.tree.nodes.get child=some node ∧ node.tag=output.tag) ∧
      TypedRetag.retagPtrValue (adapted options remaining span ctx.pointers) options.limits.retag
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base role.family.value len ActualReferenceMetadata.reference)
        ActualReferenceMetadata.reference.ty .FnEntry (Storage.withCurrent frames frame before)=
        .ok (some (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (changedPointer role.family.value role.backing.id tracker.global.nextPointerTag) len ActualReferenceMetadata.reference))
          (Storage.withCurrent frames (registeredFrame frame borrowFrame role.backing.id tracker.global.nextPointerTag)
            (installed before tracker room role.backing.id entry output.child.tree)) ∧
      (let copied := copiedFrame options remaining span frame localId valid role.family.value len
    let validCopied : localId<copied.locals.size := by simpa only [copied,copiedFrame,Array.size_set] using valid
    let doneFrame := writtenFrame options remaining span copied borrowFrame localId validCopied role.family.value len role.backing.id tracker.global.nextPointerTag
    let finalMachine := validated before tracker room role.backing.id entry output.child.tree
    ValidityMachine.validateRuntime (config options remaining span).validity () options.limits.validation
      (LocalPlaces.localRuntimePlace frames.size copied localId ActualReferenceMetadata.reference) true
      (Storage.withCurrent frames copied (ScopedFrame.entered before tracker .FnEntry)) =
      .ok () (Storage.withCurrent frames doneFrame finalMachine) ∧
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate (value options remaining span role.family.value len).imm,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames frame (ScopedFrame.entered before tracker .FnEntry)) =
      .ok () (Storage.withCurrent frames doneFrame finalMachine) ∧
    MachineHooks.withRetagMode .FnEntry
      ((ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
        ⟨.immediate (value options remaining span role.family.value len).imm,ActualReferenceMetadata.reference⟩
        (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView)
      (Storage.withCurrent frames frame before) =
      .ok () (Storage.withCurrent frames doneFrame {finalMachine with borrowTracker:=some ⟨output.global,tracker.retagMode⟩}) ∧
    finalMachine.borrowTracker=some ⟨output.global,.FnEntry⟩ ∧
    finalMachine.memory.live.find? (fun row=>row.1==role.backing.id)=some (role.backing.id,{entry with allocation:=entry.allocation.setExtra output.child.tree}) ∧
    doneFrame.extra.borrowTracker=some output.frame ∧
    doneFrame.locals.size=frame.locals.size ∧
    doneFrame.locals[localId]?.map (·.value)=some (.live (.immediate
      (value options remaining span (changedPointer role.family.value role.backing.id tracker.global.nextPointerTag) len).imm)) ∧
    finalMachine.user.payload.ghost=false ∧
    finalMachine.user.payload.payload.user.types=before.user.payload.payload.user.types ∧
    finalMachine.user.addresses=before.user.addresses ∧ finalMachine.threads=before.threads ∧
    finalMachine.dataRace=before.dataRace ) ∧
      (∀ (i : Fin role.backing.cells.size)
        (overlap : ∃byte,Window role.backing.id offset len.toNat byte ∧Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte)
        (lower upper : UInt64), offset≤lower.toNat →upper.toNat≤offset+len.toNat →
        role.backing.cells[i].offset≤lower.toNat →upper.toNat≤role.backing.cells[i].offset+role.backing.cells[i].length →
        ParentInterpretation output.child.tree (S05ConcreteProtectedChildCompletion.extend role.backing.cells[i].completion child (role.roles i overlap).grant) ∧
        OwnedOn (S05CompletedAncestryReadMutable.Authority output.child.tree
          (S05ConcreteProtectedChildCompletion.extend role.backing.cells[i].completion child (role.roles i overlap).grant)
          output.global.protectedTags child) lower upper output.child.tree.locations) := by
  dsimp only
  obtain ⟨entry,base,sourceLive,address,length,addressFits,sourceBounds,addressEq,nonnull,provenance⟩ := binding
  have present : Present (ActualWorld before) role.backing.id entry.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(role.backing.id,entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some sourceLive),rfl⟩
  have allocation := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList worldIds role.backing.id
    entry.allocation role.backing.allocation present role.backing.live
  have offsetFits : offset<2^64 := by omega
  have startEq : (UInt64.ofNat offset).toNat=offset := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt offsetFits]
  have request : Window role.backing.id offset len.toNat (role.backing.id,offset) := ⟨rfl,by omega,by omega⟩
  obtain ⟨i,cell⟩ := role.covered _ request
  have overlap : ∃byte,Window role.backing.id offset len.toNat byte ∧Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte :=
    ⟨(role.backing.id,offset),request,cell⟩
  have capability := (role.roles i overlap).issued.capability
  have bounds : (UInt64.ofNat offset).toNat+len.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat := by
    rw [startEq,capability.treeExtent,←capability.extent,←allocation]
    exact sourceBounds
  have nonzero : len≠0 := by intro zero;rw [zero] at positive;cases positive
  let output := CurrentCallSpatialEntryRead.output role borrowFrame room (UInt64.ofNat offset) len
  obtain ⟨actual,readCompleted,childCompleted,afterRuntime,capacity,growth,child,lookup,oldRoots,oldFields,node⟩ :=
    CurrentCallSpatialEntryConstructor.invoke role (by rfl) runtime distinct short nodeRoom borrowFrame room
      (UInt64.ofNat offset) len startEq rfl nonzero bounds
  have actualEntry : CandidateCurrentFnEntryRaw.operation entry.allocation.extra tracker.global borrowFrame role.backing.id
      role.family.value.provenance (UInt64.ofNat offset) len=.ok output := by rw [allocation];exact actual
  have physicalBinding : CandidateCallBindings.WindowBinding before role.family.value role.backing.id offset len.toNat :=
    ⟨entry,base,sourceLive,address,length,addressFits,sourceBounds,addressEq,nonnull,provenance⟩
  have typed := CurrentCallTypedSourceOperation.typed_of_operation options remaining span ctx before tracker frames frame borrowFrame
    enabled frameBorrow role.family.value role.backing.id offset len entry sourceLive physicalBinding positive signedFits room race
    nullComparator dynamicFuel fuelEq metadata origins output actualEntry readCompleted childCompleted
  have copied := CurrentCallTypedSourceCopy.validate_copy_of_typed_operation options limits remaining span ctx before tracker frames frame borrowFrame
    enabled frameBorrow role.family.value role.backing.id offset len entry sourceLive physicalBinding positive signedFits room race
    nullComparator dynamicFuel validationFuel fuelEq validationEq metadata origins debugOff ghostOff shallowMode output actualEntry
    readCompleted childCompleted localId valid old live cached noClocks
  obtain ⟨cellChild,cellLookup,cellModels⟩ := CurrentCallSpatialEntryConstructor.cells role (by rfl) runtime distinct short nodeRoom borrowFrame room
    (UInt64.ofNat offset) len startEq rfl nonzero bounds
  have same : cellChild=child := Option.some.inj (cellLookup.symm.trans lookup)
  subst cellChild
  exact ⟨entry,child,sourceLive,allocation,actualEntry,rfl,rfl,rfl,lookup,readCompleted,childCompleted,afterRuntime,capacity,growth,oldRoots,oldFields,node,typed.1,copied,cellModels⟩

end
end DuplicatePrefix.CurrentCallSpatialTypedSourceCopy
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialTypedSourceCopy" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial typed copy dependency {dependency}"
