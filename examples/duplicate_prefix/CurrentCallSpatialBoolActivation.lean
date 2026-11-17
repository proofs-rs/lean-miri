import duplicate_prefix.CurrentCallSpatialJointInstall
import duplicate_prefix.CurrentCallResourceBoolActivation
import duplicate_prefix.CurrentCallAllocationLicense
import duplicate_prefix.CurrentCallExclusiveWindowFrame
import duplicate_prefix.CurrentCallResourceBorrowGrowth
import duplicate_prefix.CurrentCallBoolWriteRuntime

/-! Bool activation consumes the original return role from the SAME current
joint cover. The temporary protected pointer is discarded; the original return
place remains the later store destination. -/
namespace DuplicatePrefix.CurrentCallSpatialBoolActivation
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallSpatialReturnFrame
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowFnEntryRegistration
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver CurrentCallBoolProtection
open CurrentCallTypedFnEntry ReturnProtection
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
noncomputable section

def window {machine tracker joint returnOffset place}
    (ret : RoleCover machine tracker joint .ret returnOffset 1)
    (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place)
    (physicalId : physical.id=ret.backing.id) (physicalOffset : physical.offset.toNat=returnOffset) :
    UniformWindow machine tracker (ret.roles (returnIndex ret) (returnOverlap ret)).identities 0 physical.id physical.offset.toNat 1 .ret := by
  let V := returnWindow ret
  refine ⟨V.loan,V.pointer,V.allocation,V.precise,V.loanAt,V.pointerAt,V.pointerId.trans physicalId.symm,?_,?_,V.binding,?_,V.parents,?_⟩
  · simpa only [physicalId] using V.present
  · simpa only [physicalId] using V.preciseAt
  · simpa only [physicalId] using V.issued
  · intro byte hit
    apply V.window
    simpa only [physicalId,physicalOffset] using hit

theorem activate (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (machine : Before) (tracker : MachineHooks.BorrowState) (joint : CurrentCallSpatialCover.Context machine)
    (returnOffset : Nat) (ret : RoleCover machine tracker joint .ret returnOffset 1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (state : DuplicatePrefixRuntimeInput.State machine tracker)
    (highwater : ∀ row∈machine.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag)
    (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place)
    (physicalId : physical.id=ret.backing.id) (physicalOffset : physical.offset.toNat=returnOffset)
    (pointer : physical.pointer=ret.family.value)
    (binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (short : physical.entry.allocation.extra.nodes.size+1<65536)
    (ghost : machine.user.payload.ghost=false) (race : machine.dataRace=none) (backend : machine.user.payload.payload.user.backend=.none)
    (ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1) :
    let W := window ret physical physicalId physicalOffset
    ∃ (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex),
      CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global borrowFrame physical.id W.pointer.value.provenance physical.offset 1=.ok output ∧
      output.tag=tracker.global.nextPointerTag ∧ output.global=(registered tracker.global borrowFrame physical.id fresh).1 ∧
      output.frame=(registered tracker.global borrowFrame physical.id fresh).2 ∧
      Nonempty (CurrentCallResourceFnEntry.BorrowWitness W output child physical.offset 1) ∧
    let retagged := borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry output.child.tree
    let written := output.child.tree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
      .Write (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed
    ∃ updated, (ExecutionMachine.callHooks (config options remaining span) limits).protectArgument () place
      (Storage.withCurrent frames frame machine)=
      .ok () {retagged with machine:={retagged.machine with memory:={retagged.machine.memory with live:=
        ((retagged.machine.memory.live.filter (fun row=>row.1 != physical.id)).push (physical.id,{physical.entry with allocation:=updated}))}}} ∧
      updated.extra=written.tree ∧ updated.byteSize=physical.entry.allocation.byteSize ∧ updated.len=physical.entry.allocation.len ∧
      updated.mutability=.Mut ∧ Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
        ((physical.entry.allocation.setExtra output.child.tree).setExtra written.tree)=.ok () updated ∧
      AllocationCopy.snapshot updated=AllocationCopy.snapshot physical.entry.allocation ∧
      retagged.machine.borrowTracker=some (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).extra.borrowTracker=
        some (borrowFrame.addProtector physical.id tracker.global.nextPointerTag) ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).returnPlace=frame.returnPlace := by
  let W := window ret physical physicalId physicalOffset
  have present : Present (ActualWorld machine) physical.id physical.entry.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(physical.id,physical.entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some physical.live),rfl⟩
  have ids : ((ActualWorld machine).toList.map Prod.fst).Nodup := by
    simpa only [ActualWorld,Array.toList_map,List.map_map,Function.comp_def] using state.allocationIds
  have allocation : physical.entry.allocation=W.allocation := CandidateCurrentUniformOwnerWindow.same_id _ ids physical.id _ _ present W.present
  have member := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some physical.live)
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global := by
    rw [←allocation]
    exact ⟨state.formed _ member,state.coherent _ member,state.possible _ member,highwater _ member⟩
  exact CurrentCallResourceBoolActivation.activate options limits remaining span ctx machine tracker _ 0 frames frame borrowFrame state highwater frameBorrow
    place physical W pointer allocation runtime binding fresh (by rw [←allocation];exact short) ghost race backend ready

/-- The Write contract is recovered for the SAME actual Bool operation. Full
State is used only at the constructor installation, before storage clearing. -/
private theorem write_runtime {machine tracker data owner borrowFrame place}
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place)
    (W : UniformWindow machine tracker data owner physical.id physical.offset.toNat 1 .ret)
    (allocation : physical.entry.allocation=W.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (state : DuplicatePrefixRuntimeInput.State machine tracker)
    (highwater : ∀row∈machine.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (short : W.allocation.extra.nodes.size+1<65536)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global borrowFrame physical.id W.pointer.value.provenance physical.offset 1=.ok output)
    (tag : output.tag=tracker.global.nextPointerTag) (global : output.global=(registered tracker.global borrowFrame physical.id fresh).1)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child physical.offset 1) :
    let result := output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
      .Write output.global.protectedTags .VisitChildrenOfAccessed
    DuplicatePrefixRuntimeInput.State (borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry output.child.tree).machine ⟨output.global,tracker.retagMode⟩ ∧
    result.status=.Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts result.tree output.global ∧
      ParentInterpretation result.tree (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) ∧
      GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority result.tree
        (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) output.global.protectedTags child)
        physical.offset (physical.offset+1) result.tree.locations ∧
      result.tree.nodes=output.child.tree.nodes ∧result.tree.roots=output.child.tree.roots ∧
      result.tree.tagMapping=output.child.tree.tagMapping ∧result.tree.locations.size=output.child.tree.locations.size := by
  have member := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some physical.live)
  have distinct : W.allocation.extra.roots.toList.Nodup := by rw [←allocation];exact state.roots _ member
  have oldShort : W.allocation.extra.nodes.size<65536 := by omega
  have nodeRoom : W.allocation.extra.nodes.size+1≤4294967295 := by omega
  have bounds : physical.offset.toNat+1≤W.allocation.extra.locations.size.bytes.toNat := by
    rw [←allocation,state.treeLength _ member,physical.size]
    exact physical.bounds
  have keys := CurrentCallResourceSourceKeyOrigin.operation W runtime state highwater borrowFrame fresh rfl distinct oldShort nodeRoom physical.offset 1 rfl rfl (by decide) bounds output actual
  have afterDistinct := CurrentCallResourceSourceKeyOrigin.roots W runtime state highwater borrowFrame fresh rfl distinct oldShort nodeRoom physical.offset 1 rfl rfl (by decide) bounds output actual
  let post := borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry output.child.tree
  let next : MachineHooks.BorrowState := ⟨output.global,tracker.retagMode⟩
  have enabled : post.machine.borrowTracker=some next := by
    change post.machine.borrowTracker=some ⟨output.global,tracker.retagMode⟩
    rw [global]
    rfl
  have capacity : output.child.tree.locations.size=physical.entry.allocation.extra.locations.size := by rw [allocation];exact witness.capacity
  have keyOrigin : ∀key index,(key,index)∈output.child.tree.tagMapping.mapping→key=tracker.global.nextPointerTag ∨∃old,(key,old)∈physical.entry.allocation.extra.tagMapping.mapping := by rw [allocation];exact keys
  obtain ⟨afterState,afterHighwater⟩ := CurrentCallSourceInstallState.install machine post.machine tracker next state highwater physical.id physical.entry physical.live borrowFrame fresh global
    output.child.tree witness.runtime afterDistinct capacity keyOrigin enabled rfl
  have present : Present (ActualWorld post.machine) physical.id (W.allocation.setExtra output.child.tree) := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(physical.id,{physical.entry with allocation:=physical.entry.allocation.setExtra output.child.tree}),
      Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some (MemoryCopyBridge.live_lookup_replaced machine.memory physical.id _)),by simp only [allocation]⟩
  have growth := CurrentCallResourceBorrowGrowth.operation W runtime state highwater borrowFrame fresh rfl distinct oldShort nodeRoom physical.offset 1 rfl rfl (by decide) bounds output actual
  have childBounds : physical.offset.toNat+1≤output.child.tree.locations.size.bytes.toNat := by rw [witness.capacity];exact bounds
  exact ⟨afterState,CurrentCallBoolWriteRuntime.child_write_runtime W runtime output child physical.offset 1 witness tag post.machine present
    (by rw [global];rfl) (CandidateCurrentGrantRuntime.actual_state post.machine next afterState) afterDistinct (by omega) rfl rfl childBounds .VisitChildrenOfAccessed⟩

/-- The real protectArgument and storage mutation retain selected Bool runtime
and authority, without requiring or asserting full State after clearing. -/
theorem activate_runtime (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (machine : Before) (tracker : MachineHooks.BorrowState) (joint : CurrentCallSpatialCover.Context machine)
    (returnOffset : Nat) (ret : RoleCover machine tracker joint .ret returnOffset 1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (state : DuplicatePrefixRuntimeInput.State machine tracker)
    (highwater : ∀ row∈machine.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag)
    (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place)
    (physicalId : physical.id=ret.backing.id) (physicalOffset : physical.offset.toNat=returnOffset)
    (pointer : physical.pointer=ret.family.value)
    (binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (short : physical.entry.allocation.extra.nodes.size+1<65536)
    (ghost : machine.user.payload.ghost=false) (race : machine.dataRace=none) (backend : machine.user.payload.payload.user.backend=.none)
    (ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1) :
    let W := window ret physical physicalId physicalOffset
    ∃ (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex),
      CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global borrowFrame physical.id W.pointer.value.provenance physical.offset 1=.ok output ∧
      output.tag=tracker.global.nextPointerTag ∧ output.global=(registered tracker.global borrowFrame physical.id fresh).1 ∧
      output.frame=(registered tracker.global borrowFrame physical.id fresh).2 ∧
      Nonempty (CurrentCallResourceFnEntry.BorrowWitness W output child physical.offset 1) ∧
    let retagged := borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry output.child.tree
    let written := output.child.tree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
      .Write (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed
    ∃ updated, (ExecutionMachine.callHooks (config options remaining span) limits).protectArgument () place
      (Storage.withCurrent frames frame machine)=
      .ok () {retagged with machine:={retagged.machine with memory:={retagged.machine.memory with live:=
        ((retagged.machine.memory.live.filter (fun row=>row.1 != physical.id)).push (physical.id,{physical.entry with allocation:=updated}))}}} ∧
      updated.extra=written.tree ∧ updated.byteSize=physical.entry.allocation.byteSize ∧ updated.len=physical.entry.allocation.len ∧
      updated.mutability=.Mut ∧ Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
        ((physical.entry.allocation.setExtra output.child.tree).setExtra written.tree)=.ok () updated ∧
      AllocationCopy.snapshot updated=AllocationCopy.snapshot physical.entry.allocation ∧
      retagged.machine.borrowTracker=some (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).extra.borrowTracker=
        some (borrowFrame.addProtector physical.id tracker.global.nextPointerTag) ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).returnPlace=frame.returnPlace ∧
      DuplicatePrefixRuntimeInput.State retagged.machine ⟨output.global,tracker.retagMode⟩ ∧
      written.status=.Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts written.tree output.global ∧
      ParentInterpretation written.tree (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) ∧
      GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority written.tree
        (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) output.global.protectedTags child)
        physical.offset (physical.offset+1) written.tree.locations ∧
      written.tree.nodes=output.child.tree.nodes ∧written.tree.roots=output.child.tree.roots ∧
      written.tree.tagMapping=output.child.tree.tagMapping ∧written.tree.locations.size=output.child.tree.locations.size := by
  let W := window ret physical physicalId physicalOffset
  obtain ⟨output,child,actual,tag,global,outputFrame,⟨witness⟩,updated,protect,extra,size,len,mutable,mutation,snapshot,tracked,frameTracked,returnPlace⟩ :=
    activate options limits remaining span ctx machine tracker joint returnOffset ret frames frame borrowFrame state highwater frameBorrow place physical physicalId physicalOffset pointer binding fresh short ghost race backend ready
  have present : Present (ActualWorld machine) physical.id physical.entry.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(physical.id,physical.entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some physical.live),rfl⟩
  have ids : ((ActualWorld machine).toList.map Prod.fst).Nodup := by
    simpa only [ActualWorld,Array.toList_map,List.map_map,Function.comp_def] using state.allocationIds
  have allocation : physical.entry.allocation=W.allocation := CandidateCurrentUniformOwnerWindow.same_id _ ids physical.id _ _ present W.present
  have member := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some physical.live)
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global := by
    rw [←allocation]
    exact ⟨state.formed _ member,state.coherent _ member,state.possible _ member,highwater _ member⟩
  have afterWrite := write_runtime frames frame physical W allocation runtime state highwater fresh (by rw [←allocation];exact short) output child actual tag global witness
  have equality : output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write output.global.protectedTags .VisitChildrenOfAccessed =
      output.child.tree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
        .Write (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed := by
    rw [tag,global]
    rfl
  rw [equality] at afterWrite
  exact ⟨output,child,actual,tag,global,outputFrame,⟨witness⟩,updated,protect,extra,size,len,mutable,mutation,snapshot,tracked,frameTracked,returnPlace,afterWrite⟩

private def asReturn {machine tracker joint sourceOffset sourceLength}
    (source : RoleCover machine tracker joint .mut sourceOffset sourceLength)
    (i : Fin source.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active source i)
    (byte : AllocId×Nat) (request : Window source.backing.id sourceOffset sourceLength byte)
    (cell : Window source.backing.id source.backing.cells[i].offset source.backing.cells[i].length byte) :
    UniformWindow machine tracker (source.roles i overlap).identities 0 source.backing.id byte.2 1 .ret := by
  let Q := CurrentCallSpatialRows.singleByte source i overlap byte request cell
  refine ⟨Q.loan,Q.pointer,Q.allocation,Q.precise,Q.loanAt,Q.pointerAt,Q.pointerId,Q.present,Q.preciseAt,Q.binding,Q.issued,Q.parents,?_⟩
  intro other hit
  simpa [demandOf] using Q.window other hit

private def reindex {machine tracker data owner id offset length}
    (V : UniformWindow machine tracker data owner id offset length .ret) (newId : AllocId) (same : id=newId) :
    UniformWindow machine tracker data owner newId offset length .ret := by
  refine ⟨V.loan,V.pointer,V.allocation,V.precise,V.loanAt,V.pointerAt,V.pointerId.trans same,?_,?_,V.binding,?_,V.parents,?_⟩
  · simpa only [same] using V.present
  · simpa only [same] using V.preciseAt
  · simpa only [same] using V.issued
  · intro other hit
    apply V.window
    simpa only [same] using hit

/-- One fixed Bool cell/grant drives the actual Read/constructor. Each source
cell keeps its own SAME map, extended at that SAME Bool child. The target is
one byte only to reuse the scalar frame; no operation is split at proof cells. -/
private theorem source_byte {machine tracker joint sourceOffset sourceLength returnOffset}
    (source : RoleCover machine tracker joint .mut sourceOffset sourceLength)
    (ret : RoleCover machine tracker joint .ret returnOffset 1)
    (same : source.backing.id=ret.backing.id)
    (separate : ∀byte,Window source.backing.id sourceOffset sourceLength byte→Window ret.backing.id returnOffset 1 byte→False)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts ret.backing.allocation.extra tracker.global)
    (distinct : ret.backing.allocation.extra.roots.toList.Nodup) (short : ret.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : ret.backing.allocation.extra.nodes.size+1≤4294967295)
    (borrowFrame : FrameState) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (start : UInt64) (startEq : start.toNat=returnOffset)
    (bounds : start.toNat+1≤ret.backing.allocation.extra.locations.size.bytes.toNat)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (entryEq : entry.allocation=ret.backing.allocation)
    (i : Fin source.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active source i)
    (byte : AllocId×Nat) (request : Window source.backing.id sourceOffset sourceLength byte)
    (cell : Window source.backing.id source.backing.cells[i].offset source.backing.cells[i].length byte) :
    let V := reindex (asReturn source i overlap byte request cell) ret.backing.id same
    let output := CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1
    ∃child,output.child.tree.indexOfTag output.tag=some child ∧
      Nonempty (UniformWindow (CurrentCallSpatialSourceInstall.copiedMachine ret borrowFrame fresh start 1 entry)
        ⟨output.global,tracker.retagMode⟩
        (windowData ret.backing.id V.pointer (S05ConcreteProtectedChildCompletion.extend V.precise.completion child (ret.roles (returnIndex ret) (returnOverlap ret)).grant))
        0 ret.backing.id byte.2 1 .ret) := by
  let V := reindex (asReturn source i overlap byte request cell) ret.backing.id same
  have allocationEq : V.allocation=ret.backing.allocation := by
    change source.backing.allocation=ret.backing.allocation
    exact congrArg AllocationCover.allocation (joint.same_backing source.backingAt ret.backingAt same)
  have disjoint : ∀other,Window ret.backing.id returnOffset 1 other→Window ret.backing.id byte.2 1 other→False := by
    intro other boolHit pointHit
    have pointEq : other.2=byte.2 := by have := pointHit.2;omega
    apply separate other
    · refine ⟨pointHit.1.trans same.symm,?_,?_⟩
      · rw [pointEq]
        exact request.2.1
      · rw [pointEq]
        exact request.2.2
    · exact boolHit
  exact CurrentCallSpatialReturnFrame.same_selected ret V allocationEq disjoint rfl runtime distinct short nodeRoom borrowFrame fresh start 1 startEq rfl (by decide) bounds
    (returnIndex ret) (returnOverlap ret) entry entryEq

open Lean Elab Tactic in
elab "spatial_bool_rule " suffix:str : term => do
  let found := (←getEnv).constants.toList.filter (fun (name,_)=>name.toString.endsWith suffix.getString)
  match found with | [(name,_)]=>return mkConst name | _=>throwError "expected checked Bool-frame theorem {suffix.getString}"

/-- A source-byte certificate survives the actual disjoint ranged Write and
actual writeUninit allocation replacement. No post-clear State is required. -/
private theorem after_write_byte {before tracker data owner id off}
    (V : UniformWindow before tracker data owner id off 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts V.allocation.extra tracker.global)
    (provenance : ProvenanceExtra) (offset amount : Size) (visit : ChildrenVisitMode)
    (bounds : offset.bytes.toNat+amount.bytes.toNat≤V.allocation.extra.locations.size.bytes.toNat)
    (capacity : (V.allocation.extra.performBorrowAccessRange provenance offset amount .Write tracker.global.protectedTags visit).tree.locations.size=V.allocation.extra.locations.size)
    (lower upper : UInt64) (lowerEq : lower.toNat=off) (upperEq : upper.toNat=off+1)
    (disjoint : ∀point : UInt64,lower.toNat≤point.toNat→point.toNat<upper.toNat→point.toNat<offset.bytes.toNat ∨(offset.bytes+amount.bytes).toNat≤point.toNat)
    (post : Before) (next : MachineHooks.BorrowState) (updated : Allocation Provenance BorrowTree)
    (present : Present (ActualWorld post) id updated)
    (rootTag : next.global.rootTag? id=tracker.global.rootTag? id)
    (flags : next.global.protectedTags=tracker.global.protectedTags)
    (extra : updated.extra=(V.allocation.extra.performBorrowAccessRange provenance offset amount .Write tracker.global.protectedTags visit).tree)
    (len : updated.len=V.allocation.len) (size : updated.byteSize=V.allocation.byteSize)
    (afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts updated.extra next.global) :
    ∃Q : UniformWindow post next data owner id off 1 .ret,Q.allocation=updated ∧Q.pointer=V.pointer ∧Q.precise=V.precise := by
  let written := V.allocation.extra.performBorrowAccessRange provenance offset amount .Write tracker.global.protectedTags visit
  have frame := GeneralBorrowFreshReadFrame.frame V.allocation.extra provenance offset amount .Write tracker.global.protectedTags visit
  have nodeFrame := congrArg BorrowTree.nodes frame
  have nodes : written.tree.nodes=V.allocation.extra.nodes := nodeFrame
  have rootFrame := congrArg BorrowTree.roots frame
  have roots : written.tree.roots=V.allocation.extra.roots := rootFrame
  have tagFrame := congrArg BorrowTree.tagMapping frame
  have tags : written.tree.tagMapping=V.allocation.extra.tagMapping := tagFrame
  have initial := (spatial_bool_rule ".CurrentCallResourceFnEntry.window_owned") V (by rfl) runtime lower upper (by omega) (by omega)
  have resultRuntime : DuplicatePrefixBorrowContract.RuntimeFacts written.tree next.global := by rw [extra] at afterRuntime;exact afterRuntime
  have retained := (CurrentCallExclusiveWindowFrame.write_outside V.allocation.extra V.precise.completion tracker.global.protectedTags V.pointer.grant provenance offset amount visit lower upper runtime.formed.well bounds disjoint initial).2
  have parents : ParentInterpretation updated.extra V.precise.completion := by
    rw [extra,frame]
    exact (spatial_bool_rule ".CurrentCallSpatialReturnFrame.parents_locations") V.allocation.extra _ V.precise.completion V.parents
  have issued := CurrentCallAllocationLicense.spatial V.issued post next updated present rootTag len size
    (by rw [extra];exact capacity)
    (by intro position root found;rw [extra,roots];exact found)
    (by intro index node found;refine ⟨node,?_,rfl,rfl,rfl,rfl⟩;rw [extra,nodes];exact found)
    V.precise.completion (by intros;assumption)
  have binding : PointerBinds updated V.pointer := by
    obtain ⟨node,nodeAt,_,value⟩ := V.binding
    have foundAt : updated.extra.nodes.get V.pointer.grant=some node := by rw [extra,nodes];exact nodeAt
    exact ⟨node,foundAt,afterRuntime.formed.allocator.nodeTags _ _ foundAt,value⟩
  refine ⟨⟨V.loan,V.pointer,updated,V.precise,V.loanAt,V.pointerAt,V.pointerId,present,V.preciseAt,binding,issued,parents,?_⟩,rfl,rfl,rfl⟩
  intro byte inside
  refine ⟨by rw [len];exact (V.window byte inside).1,?_⟩
  intro segment member lo hi index node nodeAt
  have writtenMember : segment∈written.tree.locations.entries.toList := by rw [extra] at member;exact member
  obtain ⟨position,valid,same⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp writtenMember)
  subst segment
  have byteEq : byte.2=off := by have := inside.2;omega
  dsimp only [written] at lo hi valid
  have rights := retained position valid (by omega) (by rw [upperEq];omega) (by rw [lowerEq];omega) index node (by rw [extra] at nodeAt;exact nodeAt)
  have writtenAt : written.tree.nodes.get index=some node := by rw [extra] at nodeAt;exact nodeAt
  have rowPossible := resultRuntime.possible position valid index node writtenAt
  have rowProfile := (resultRuntime.formed.profile position valid).present index node writtenAt
  have realized := CandidateCurrentGrantRuntime.realized _ _ rowPossible rowProfile
  rw [flags] at realized
  rw [flags]
  constructor
  · intro below
    exact (spatial_bool_rule ".CurrentCallResourceFnEntry.local_token") _ _ realized (rights.1 below)
  · intro clash
    apply Classical.byContradiction
    intro outside
    exact (spatial_bool_rule ".CurrentCallResourceFnEntry.foreign_no_clash") _ _ realized (rights.2 outside) clash

private def boolWrite {machine tracker joint returnOffset}
    (ret : RoleCover machine tracker joint .ret returnOffset 1) (borrowFrame : FrameState)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615) (start : UInt64) :=
  let output := CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1
  output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes start) (Size.ofBytes 1)
    .Write output.global.protectedTags .VisitChildrenOfAccessed

/-- Universal source-cell framing for the SAME one Bool operation. The child,
Bool origin and each cell completion are fixed before quantifying source bytes. -/
private theorem source_after_same {machine tracker joint sourceOffset sourceLength returnOffset}
    (source : RoleCover machine tracker joint .mut sourceOffset sourceLength)
    (ret : RoleCover machine tracker joint .ret returnOffset 1)
    (same : source.backing.id=ret.backing.id)
    (separate : ∀byte,Window source.backing.id sourceOffset sourceLength byte→Window ret.backing.id returnOffset 1 byte→False)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts ret.backing.allocation.extra tracker.global)
    (distinct : ret.backing.allocation.extra.roots.toList.Nodup) (short : ret.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : ret.backing.allocation.extra.nodes.size+1≤4294967295)
    (borrowFrame : FrameState) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (start : UInt64) (startEq : start.toNat=returnOffset)
    (bounds : start.toNat+1≤ret.backing.allocation.extra.locations.size.bytes.toNat)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (entryEq : entry.allocation=ret.backing.allocation)
    (child : UniIndex)
    (lookup : (CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).child.tree.indexOfTag tracker.global.nextPointerTag=some child)
    (ctorState : DuplicatePrefixRuntimeInput.State (CurrentCallSpatialSourceInstall.copiedMachine ret borrowFrame fresh start 1 entry)
      ⟨(CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).global,tracker.retagMode⟩)
    (ctorRuntime : DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).child.tree
      (CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).global)
    (ctorCapacity : (CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).child.tree.locations.size=ret.backing.allocation.extra.locations.size)
    (writeCapacity : (boolWrite ret borrowFrame fresh start).tree.locations.size=(CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).child.tree.locations.size)
    (post : Before) (updated : Allocation Provenance BorrowTree) (present : Present (ActualWorld post) ret.backing.id updated)
    (extra : updated.extra=(boolWrite ret borrowFrame fresh start).tree)
    (len : updated.len=ret.backing.allocation.len) (size : updated.byteSize=ret.backing.allocation.byteSize)
    (afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts updated.extra (CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).global) :
    ∀(i : Fin source.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active source i)
      (byte : AllocId×Nat) (request : Window source.backing.id sourceOffset sourceLength byte)
      (cell : Window source.backing.id source.backing.cells[i].offset source.backing.cells[i].length byte),
      ∃Q : UniformWindow post ⟨(CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).global,tracker.retagMode⟩
        (windowData ret.backing.id (source.family.at (source.roles i overlap).grant)
          (S05ConcreteProtectedChildCompletion.extend source.backing.cells[i].completion child (ret.roles (returnIndex ret) (returnOverlap ret)).grant))
        0 ret.backing.id byte.2 1 .ret,
        Q.allocation=updated ∧Q.pointer=source.family.at (source.roles i overlap).grant ∧
        Q.precise.completion=S05ConcreteProtectedChildCompletion.extend source.backing.cells[i].completion child (ret.roles (returnIndex ret) (returnOverlap ret)).grant := by
  intro i overlap byte request cell
  obtain ⟨other,otherLookup,⟨V⟩⟩ := source_byte source ret same separate runtime distinct short nodeRoom borrowFrame fresh start startEq bounds entry entryEq i overlap byte request cell
  have equal : other=child := Option.some.inj (otherLookup.symm.trans lookup)
  subst other
  change UniformWindow (CurrentCallSpatialSourceInstall.copiedMachine ret borrowFrame fresh start 1 entry)
    ⟨(CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).global,tracker.retagMode⟩
    (windowData ret.backing.id (source.family.at (source.roles i overlap).grant)
      (S05ConcreteProtectedChildCompletion.extend source.backing.cells[i].completion child (ret.roles (returnIndex ret) (returnOverlap ret)).grant))
    0 ret.backing.id byte.2 1 .ret at V
  have fields := (spatial_bool_rule ".CurrentCallSpatialJointInstall.canonical_fields") _ _ V
  have ids : ((ActualWorld (CurrentCallSpatialSourceInstall.copiedMachine ret borrowFrame fresh start 1 entry)).toList.map Prod.fst).Nodup := by
    simpa only [ActualWorld,Array.toList_map,List.map_map,Function.comp_def] using ctorState.allocationIds
  have known := CurrentCallSpatialSourceInstall.copied_present ret borrowFrame fresh start 1 entry entryEq
  have allocationEq : V.allocation=ret.backing.allocation.setExtra (CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).child.tree :=
    CandidateCurrentUniformOwnerWindow.same_id _ ids ret.backing.id _ _ V.present known
  have currentRuntime : DuplicatePrefixBorrowContract.RuntimeFacts V.allocation.extra (CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).global := by
    rw [allocationEq]
    exact ctorRuntime
  have pointBound := (V.window (ret.backing.id,byte.2) ⟨rfl,Nat.le_refl _,by omega⟩).1
  have fits : byte.2+1<2^64 := by have := V.issued.capability.extent;have := UInt64.toNat_lt V.allocation.byteSize.bytes;omega
  let lower := UInt64.ofNat byte.2
  let upper := UInt64.ofNat (byte.2+1)
  have lowerEq : lower.toNat=byte.2 := by simp only [lower,UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by omega : byte.2<2^64)]
  have upperEq : upper.toNat=byte.2+1 := by simp only [upper,UInt64.toNat_ofNat',Nat.mod_eq_of_lt fits]
  have boolEnd : (start+1).toNat=returnOffset+1 := by
    have noWrap : start.toNat+1<2^64 := Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt ret.backing.allocation.extra.locations.size.bytes)
    rw [UInt64.toNat_add,startEq,show (1:UInt64).toNat=1 from rfl,Nat.mod_eq_of_lt (by omega)]
  have disjoint : ∀point : UInt64,lower.toNat≤point.toNat→point.toNat<upper.toNat→point.toNat<start.toNat ∨(start+1).toNat≤point.toNat := by
    intro point lo hi
    have pointEq : point.toNat=byte.2 := by omega
    by_cases early : point.toNat<start.toNat
    · exact Or.inl early
    · apply Or.inr
      apply Nat.le_of_not_gt
      intro inside
      apply separate (ret.backing.id,point.toNat)
      · exact ⟨same.symm,by rw [pointEq];exact request.2.1,by rw [pointEq];exact request.2.2⟩
      · exact ⟨rfl,by omega,by omega⟩
  have writeBounds : start.toNat+1≤V.allocation.extra.locations.size.bytes.toNat := by rw [allocationEq];exact ctorCapacity ▸ bounds
  obtain ⟨Q,actualAllocation,actualPointer,actualPrecise⟩ := after_write_byte V currentRuntime (.concrete tracker.global.nextPointerTag) (Size.ofBytes start) (Size.ofBytes 1) .VisitChildrenOfAccessed writeBounds
    (by simpa only [allocationEq,Allocation.setExtra,Allocation.mapExtra,boolWrite,CurrentCallSpatialEntryRead.output] using writeCapacity)
    lower upper lowerEq upperEq disjoint post ⟨(CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).global,tracker.retagMode⟩ updated present rfl rfl
    (by simpa only [allocationEq,Allocation.setExtra,Allocation.mapExtra,boolWrite,CurrentCallSpatialEntryRead.output] using extra)
    (by simpa only [allocationEq,Allocation.setExtra,Allocation.mapExtra,Allocation.len] using len)
    (by simpa only [allocationEq,Allocation.setExtra,Allocation.mapExtra,Allocation.byteSize] using size) afterRuntime
  exact ⟨Q,actualAllocation,actualPointer.trans fields.1,(congrArg PreciseAllocation.completion actualPrecise).trans fields.2⟩

private theorem state_projection {before after : Before} {tracker : MachineHooks.BorrowState}
    (state : DuplicatePrefixRuntimeInput.State before tracker) (memory : after.memory=before.memory)
    (tracked : after.borrowTracker=some tracker) : DuplicatePrefixRuntimeInput.State after tracker := by
  refine ⟨tracked,?_,state.cachedRootIds,state.cachedRootTags,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [memory] using state.allocationIds
  · simpa only [memory] using state.tags
  · simpa only [memory] using state.formed
  · simpa only [memory] using state.roots
  · simpa only [memory] using state.coherent
  · simpa only [memory] using state.possible
  · simpa only [memory] using state.byteLength
  · simpa only [memory] using state.maskValid
  · simpa only [memory] using state.maskLength
  · simpa only [memory] using state.provenance
  · simpa only [memory] using state.treeLength

private def afterMachine {machine place}
    (retagged : RootState) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place)
    (updated : Allocation Provenance BorrowTree) : Before :=
  {retagged.machine with memory:={retagged.machine.memory with live:=
    ((retagged.machine.memory.live.filter (fun row=>row.1 != physical.id)).push (physical.id,{physical.entry with allocation:=updated}))}}

/-- SAME-allocation activation immediately retains every fixed source cell on
its ACTUAL updated allocation. All source-byte certificates share one B child. -/
theorem activate_same (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (machine : Before) (tracker : MachineHooks.BorrowState) (joint : CurrentCallSpatialCover.Context machine)
    (returnOffset : Nat) (ret : RoleCover machine tracker joint .ret returnOffset 1)
    (sourceOffset sourceLength : Nat) (source : RoleCover machine tracker joint .mut sourceOffset sourceLength)
    (same : source.backing.id=ret.backing.id)
    (separate : ∀byte,Window source.backing.id sourceOffset sourceLength byte→Window ret.backing.id returnOffset 1 byte→False)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (state : DuplicatePrefixRuntimeInput.State machine tracker)
    (highwater : ∀ row∈machine.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag)
    (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place)
    (physicalId : physical.id=ret.backing.id) (physicalOffset : physical.offset.toNat=returnOffset)
    (pointer : physical.pointer=ret.family.value)
    (binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (short : physical.entry.allocation.extra.nodes.size+1<65536)
    (ghost : machine.user.payload.ghost=false) (race : machine.dataRace=none) (backend : machine.user.payload.payload.user.backend=.none)
    (ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1) :
    let W := window ret physical physicalId physicalOffset
    ∃ (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex),
      CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global borrowFrame physical.id W.pointer.value.provenance physical.offset 1=.ok output ∧
      output.tag=tracker.global.nextPointerTag ∧ output.global=(registered tracker.global borrowFrame physical.id fresh).1 ∧
      output.frame=(registered tracker.global borrowFrame physical.id fresh).2 ∧
      Nonempty (CurrentCallResourceFnEntry.BorrowWitness W output child physical.offset 1) ∧
    let retagged := borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry output.child.tree
    let written := output.child.tree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
      .Write (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed
    ∃ updated, (ExecutionMachine.callHooks (config options remaining span) limits).protectArgument () place
      (Storage.withCurrent frames frame machine)=
      .ok () {retagged with machine:={retagged.machine with memory:={retagged.machine.memory with live:=
        ((retagged.machine.memory.live.filter (fun row=>row.1 != physical.id)).push (physical.id,{physical.entry with allocation:=updated}))}}} ∧
      updated.extra=written.tree ∧ updated.byteSize=physical.entry.allocation.byteSize ∧ updated.len=physical.entry.allocation.len ∧
      updated.mutability=.Mut ∧ Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
        ((physical.entry.allocation.setExtra output.child.tree).setExtra written.tree)=.ok () updated ∧
      AllocationCopy.snapshot updated=AllocationCopy.snapshot physical.entry.allocation ∧
      retagged.machine.borrowTracker=some (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).extra.borrowTracker=
        some (borrowFrame.addProtector physical.id tracker.global.nextPointerTag) ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).returnPlace=frame.returnPlace ∧
      DuplicatePrefixRuntimeInput.State retagged.machine ⟨output.global,tracker.retagMode⟩ ∧
      written.status=.Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts written.tree output.global ∧
      ParentInterpretation written.tree (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) ∧
      GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority written.tree
        (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) output.global.protectedTags child)
        physical.offset (physical.offset+1) written.tree.locations ∧
      written.tree.nodes=output.child.tree.nodes ∧written.tree.roots=output.child.tree.roots ∧
      written.tree.tagMapping=output.child.tree.tagMapping ∧written.tree.locations.size=output.child.tree.locations.size ∧
      ∀(i : Fin source.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active source i)
        (byte : AllocId×Nat) (request : Window source.backing.id sourceOffset sourceLength byte)
        (cell : Window source.backing.id source.backing.cells[i].offset source.backing.cells[i].length byte),
        ∃Q : UniformWindow (afterMachine retagged physical updated) ⟨output.global,tracker.retagMode⟩
          (windowData ret.backing.id (source.family.at (source.roles i overlap).grant)
            (S05ConcreteProtectedChildCompletion.extend source.backing.cells[i].completion child (ret.roles (returnIndex ret) (returnOverlap ret)).grant))
          0 ret.backing.id byte.2 1 .ret,
          Q.allocation=updated ∧Q.pointer=source.family.at (source.roles i overlap).grant ∧
          Q.precise.completion=S05ConcreteProtectedChildCompletion.extend source.backing.cells[i].completion child (ret.roles (returnIndex ret) (returnOverlap ret)).grant := by
  let W := window ret physical physicalId physicalOffset
  obtain ⟨output,child,actual,tag,global,outputFrame,⟨witness⟩,updated,protect,extra,size,len,mutable,mutation,snapshot,tracked,frameTracked,returnPlace,ctorState,writeDone,writeRuntime,writeParents,writeOwned,writeNodes,writeRoots,writeTags,writeCapacity⟩ :=
    activate_runtime options limits remaining span ctx machine tracker joint returnOffset ret frames frame borrowFrame state highwater frameBorrow place physical physicalId physicalOffset pointer binding fresh short ghost race backend ready
  have actualRet : CandidateCurrentFnEntryRaw.operation ret.backing.allocation.extra tracker.global borrowFrame ret.backing.id ret.family.value.provenance physical.offset 1=.ok output := by
    change CandidateCurrentFnEntryRaw.operation ret.backing.allocation.extra tracker.global borrowFrame physical.id ret.family.value.provenance physical.offset 1=.ok output at actual
    simpa only [physicalId] using actual
  have outputEq : output=CurrentCallSpatialEntryRead.output ret borrowFrame fresh physical.offset 1 :=
    Except.ok.inj (actualRet.symm.trans (CurrentCallSpatialEntryRead.literal_operation ret borrowFrame fresh physical.offset 1))
  subst output
  have present : Present (ActualWorld machine) physical.id physical.entry.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(physical.id,physical.entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some physical.live),rfl⟩
  have ids : ((ActualWorld machine).toList.map Prod.fst).Nodup := by simpa only [ActualWorld,Array.toList_map,List.map_map,Function.comp_def] using state.allocationIds
  have entryEq : physical.entry.allocation=ret.backing.allocation := CandidateCurrentUniformOwnerWindow.same_id _ ids physical.id _ _ present (by simpa only [physicalId,Present] using ret.backing.live)
  have member := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some physical.live)
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts ret.backing.allocation.extra tracker.global := by
    rw [←entryEq]
    exact ⟨state.formed _ member,state.coherent _ member,state.possible _ member,highwater _ member⟩
  have distinct : ret.backing.allocation.extra.roots.toList.Nodup := by rw [←entryEq];exact state.roots _ member
  have oldShort : ret.backing.allocation.extra.nodes.size<65536 := by rw [←entryEq];omega
  have nodeRoom : ret.backing.allocation.extra.nodes.size+1≤4294967295 := by omega
  have bounds : physical.offset.toNat+1≤ret.backing.allocation.extra.locations.size.bytes.toNat := by
    rw [←entryEq,state.treeLength _ member,physical.size]
    exact physical.bounds
  let output := CurrentCallSpatialEntryRead.output ret borrowFrame fresh physical.offset 1
  let retagged := borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry output.child.tree
  have memoryEq : (CurrentCallSpatialSourceInstall.copiedMachine ret borrowFrame fresh physical.offset 1 physical.entry).memory=retagged.machine.memory := by
    change RetagEntry.updatedMemory machine.memory ret.backing.id physical.entry output.child.tree=RetagEntry.updatedMemory machine.memory physical.id physical.entry output.child.tree
    rw [physicalId]
  have canonicalState : DuplicatePrefixRuntimeInput.State (CurrentCallSpatialSourceInstall.copiedMachine ret borrowFrame fresh physical.offset 1 physical.entry) ⟨output.global,tracker.retagMode⟩ :=
    state_projection ctorState memoryEq rfl
  have known : Present (ActualWorld (afterMachine retagged physical updated)) ret.backing.id updated := by
    have live : (afterMachine retagged physical updated).memory.live.find? (fun row=>row.1==physical.id)=some (physical.id,{physical.entry with allocation:=updated}) :=
      MemoryCopyBridge.live_lookup_replaced retagged.machine.memory physical.id _
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(physical.id,{physical.entry with allocation:=updated}),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),by simp only [physicalId]⟩
  have sourceFrames := source_after_same source ret same separate runtime distinct oldShort nodeRoom borrowFrame fresh physical.offset physicalOffset bounds physical.entry entryEq child
    (by have found:=witness.runtime.formed.allocator.nodeTags child witness.node witness.nodeAt;rw [witness.tag] at found;exact found)
    canonicalState witness.runtime witness.capacity writeCapacity (afterMachine retagged physical updated) updated known extra
    (by rw [entryEq] at len;exact len) (by rw [entryEq] at size;exact size) (by rw [extra];exact writeRuntime)
  exact ⟨output,child,actual,tag,global,outputFrame,⟨witness⟩,updated,protect,extra,size,len,mutable,mutation,snapshot,tracked,frameTracked,returnPlace,ctorState,writeDone,writeRuntime,writeParents,writeOwned,writeNodes,writeRoots,writeTags,writeCapacity,sourceFrames⟩

private theorem other_present_final {machine place}
    (retagged : RootState) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place)
    (tree : BorrowTree) (memory : retagged.machine.memory=RetagEntry.updatedMemory machine.memory physical.id physical.entry tree)
    (updated : Allocation Provenance BorrowTree) (id : AllocId) (allocation : Allocation Provenance BorrowTree)
    (old : Present (ActualWorld machine) id allocation) (different : id≠physical.id) :
    Present (ActualWorld (afterMachine retagged physical updated)) id allocation := by
  simp only [Present,ActualWorld,Array.toList_map] at old ⊢
  obtain ⟨row,member,same⟩ := List.mem_map.mp old
  have idEq : row.1=id := (Prod.mk.inj same).1
  have inner : row∈retagged.machine.memory.live := by
    rw [memory]
    apply Array.mem_push.mpr
    apply Or.inl
    apply Array.mem_filter.mpr
    exact ⟨Array.mem_toList_iff.mp member,by simpa only [idEq,bne_iff_ne] using different⟩
  apply List.mem_map.mpr
  refine ⟨row,?_,same⟩
  apply Array.mem_toList_iff.mpr
  apply Array.mem_push.mpr
  apply Or.inl
  apply Array.mem_filter.mpr
  exact ⟨inner,by simpa only [idEq,bne_iff_ne] using different⟩

private theorem other_transport {machine tracker data owner id off}
    (V : UniformWindow machine tracker data owner id off 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts V.allocation.extra tracker.global)
    (borrowFrame : FrameState) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (boolId : AllocId) (post : Before) (next : MachineHooks.BorrowState)
    (global : next.global=(registered tracker.global borrowFrame boolId fresh).1)
    (present : Present (ActualWorld post) id V.allocation) :
    ∃Q : UniformWindow post next data owner id off 1 .ret,Q.allocation=V.allocation ∧Q.pointer=V.pointer ∧Q.precise=V.precise := by
  let current := CurrentCallResourceFnEntry.registered_window V runtime borrowFrame fresh
  have fields := (spatial_bool_rule ".CurrentCallSpatialEntryRead.registered_window_fields") V runtime borrowFrame fresh
  have issued := CurrentCallAllocationLicense.spatial V.issued post next V.allocation present (by rw [global];rfl) rfl rfl rfl
    (by intros;assumption) (by intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩) V.precise.completion (by intros;assumption)
  refine ⟨⟨V.loan,V.pointer,V.allocation,V.precise,V.loanAt,V.pointerAt,V.pointerId,present,V.preciseAt,V.binding,issued,V.parents,?_⟩,rfl,rfl,rfl⟩
  intro byte inside
  have available := current.window byte inside
  rw [fields.1,fields.2.1,fields.2.2] at available
  rw [global]
  exact available

/-- Other source allocations retain the SAME source cells and pointer families
through the actual Bool protection/writeUninit, including fresh global flags. -/
theorem activate_other (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (machine : Before) (tracker : MachineHooks.BorrowState) (joint : CurrentCallSpatialCover.Context machine)
    (returnOffset : Nat) (ret : RoleCover machine tracker joint .ret returnOffset 1)
    (sourceOffset sourceLength : Nat) (source : RoleCover machine tracker joint .mut sourceOffset sourceLength)
    (different : source.backing.id≠ret.backing.id)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (state : DuplicatePrefixRuntimeInput.State machine tracker)
    (highwater : ∀ row∈machine.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag)
    (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place)
    (physicalId : physical.id=ret.backing.id) (physicalOffset : physical.offset.toNat=returnOffset)
    (pointer : physical.pointer=ret.family.value)
    (binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (short : physical.entry.allocation.extra.nodes.size+1<65536)
    (ghost : machine.user.payload.ghost=false) (race : machine.dataRace=none) (backend : machine.user.payload.payload.user.backend=.none)
    (ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1) :
    let W := window ret physical physicalId physicalOffset
    ∃ (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex),
      CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global borrowFrame physical.id W.pointer.value.provenance physical.offset 1=.ok output ∧
      output.tag=tracker.global.nextPointerTag ∧ output.global=(registered tracker.global borrowFrame physical.id fresh).1 ∧
      output.frame=(registered tracker.global borrowFrame physical.id fresh).2 ∧
      Nonempty (CurrentCallResourceFnEntry.BorrowWitness W output child physical.offset 1) ∧
    let retagged := borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry output.child.tree
    let written := output.child.tree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
      .Write (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed
    ∃ updated, (ExecutionMachine.callHooks (config options remaining span) limits).protectArgument () place
      (Storage.withCurrent frames frame machine)=
      .ok () {retagged with machine:={retagged.machine with memory:={retagged.machine.memory with live:=
        ((retagged.machine.memory.live.filter (fun row=>row.1 != physical.id)).push (physical.id,{physical.entry with allocation:=updated}))}}} ∧
      updated.extra=written.tree ∧ updated.byteSize=physical.entry.allocation.byteSize ∧ updated.len=physical.entry.allocation.len ∧
      updated.mutability=.Mut ∧ Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
        ((physical.entry.allocation.setExtra output.child.tree).setExtra written.tree)=.ok () updated ∧
      AllocationCopy.snapshot updated=AllocationCopy.snapshot physical.entry.allocation ∧
      retagged.machine.borrowTracker=some (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).extra.borrowTracker=
        some (borrowFrame.addProtector physical.id tracker.global.nextPointerTag) ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).returnPlace=frame.returnPlace ∧
      DuplicatePrefixRuntimeInput.State retagged.machine ⟨output.global,tracker.retagMode⟩ ∧
      written.status=.Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts written.tree output.global ∧
      ParentInterpretation written.tree (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) ∧
      GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority written.tree
        (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) output.global.protectedTags child)
        physical.offset (physical.offset+1) written.tree.locations ∧
      written.tree.nodes=output.child.tree.nodes ∧written.tree.roots=output.child.tree.roots ∧
      written.tree.tagMapping=output.child.tree.tagMapping ∧written.tree.locations.size=output.child.tree.locations.size ∧
      ∀(i : Fin source.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active source i)
        (byte : AllocId×Nat) (request : Window source.backing.id sourceOffset sourceLength byte)
        (cell : Window source.backing.id source.backing.cells[i].offset source.backing.cells[i].length byte),
        ∃Q : UniformWindow (afterMachine retagged physical updated) ⟨output.global,tracker.retagMode⟩
          (source.roles i overlap).identities 0 source.backing.id byte.2 1 .ret,
          Q.allocation=source.backing.allocation ∧Q.pointer=source.family.at (source.roles i overlap).grant ∧Q.precise.completion=source.backing.cells[i].completion := by
  obtain ⟨output,child,actual,tag,global,outputFrame,⟨witness⟩,updated,protect,extra,size,len,mutable,mutation,snapshot,tracked,frameTracked,returnPlace,ctorState,writeDone,writeRuntime,writeParents,writeOwned,writeNodes,writeRoots,writeTags,writeCapacity⟩ :=
    activate_runtime options limits remaining span ctx machine tracker joint returnOffset ret frames frame borrowFrame state highwater frameBorrow place physical physicalId physicalOffset pointer binding fresh short ghost race backend ready
  let retagged := borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry output.child.tree
  have present : Present (ActualWorld (afterMachine retagged physical updated)) source.backing.id source.backing.allocation :=
    other_present_final retagged physical output.child.tree rfl updated source.backing.id source.backing.allocation source.backing.live (by simpa only [physicalId] using different)
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts source.backing.allocation.extra tracker.global :=
    (spatial_bool_rule ".CurrentCallSpatialJointInstall.runtime_present") state highwater source.backing.id source.backing.allocation source.backing.live
  refine ⟨output,child,actual,tag,global,outputFrame,⟨witness⟩,updated,protect,extra,size,len,mutable,mutation,snapshot,tracked,frameTracked,returnPlace,ctorState,writeDone,writeRuntime,writeParents,writeOwned,writeNodes,writeRoots,writeTags,writeCapacity,?_⟩
  intro i overlap byte request cell
  let V := asReturn source i overlap byte request cell
  have runtimeV : DuplicatePrefixBorrowContract.RuntimeFacts V.allocation.extra tracker.global := runtime
  obtain ⟨Q,allocationEq,pointerEq,preciseEq⟩ := other_transport V runtimeV borrowFrame fresh physical.id (afterMachine retagged physical updated)
    ⟨output.global,tracker.retagMode⟩ global present
  exact ⟨Q,allocationEq,pointerEq,congrArg PreciseAllocation.completion preciseEq⟩

private theorem reindex_fields {machine tracker data owner id offset length}
    (V : UniformWindow machine tracker data owner id offset length .ret) (newId : AllocId) (same : id=newId) :
    (reindex V newId same).allocation=V.allocation ∧(reindex V newId same).pointer=V.pointer ∧(reindex V newId same).precise=V.precise := by
  unfold reindex
  exact ⟨rfl,rfl,rfl⟩

/-- One actual Bool activation retains the complete selected source cover.
Every output completion is the fixed old cell map (or its SAME Bool edge),
independent of the source byte. This is not old-Bool authority while held. -/
theorem activate_sources (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (machine : Before) (tracker : MachineHooks.BorrowState) (joint : CurrentCallSpatialCover.Context machine)
    (returnOffset : Nat) (ret : RoleCover machine tracker joint .ret returnOffset 1)
    (sourceOffset sourceLength : Nat) (source : RoleCover machine tracker joint .mut sourceOffset sourceLength)
    (separate : ∀byte,Window source.backing.id sourceOffset sourceLength byte→Window ret.backing.id returnOffset 1 byte→False)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (state : DuplicatePrefixRuntimeInput.State machine tracker)
    (highwater : ∀ row∈machine.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag)
    (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place)
    (physicalId : physical.id=ret.backing.id) (physicalOffset : physical.offset.toNat=returnOffset)
    (pointer : physical.pointer=ret.family.value)
    (binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (short : physical.entry.allocation.extra.nodes.size+1<65536)
    (ghost : machine.user.payload.ghost=false) (race : machine.dataRace=none) (backend : machine.user.payload.payload.user.backend=.none)
    (ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1) :
    let W := window ret physical physicalId physicalOffset
    ∃ (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex),
      CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global borrowFrame physical.id W.pointer.value.provenance physical.offset 1=.ok output ∧
      output.tag=tracker.global.nextPointerTag ∧ output.global=(registered tracker.global borrowFrame physical.id fresh).1 ∧
      output.frame=(registered tracker.global borrowFrame physical.id fresh).2 ∧
      Nonempty (CurrentCallResourceFnEntry.BorrowWitness W output child physical.offset 1) ∧
    let retagged := borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry output.child.tree
    let written := output.child.tree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
      .Write (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed
    ∃ updated, (ExecutionMachine.callHooks (config options remaining span) limits).protectArgument () place
      (Storage.withCurrent frames frame machine)=
      .ok () {retagged with machine:={retagged.machine with memory:={retagged.machine.memory with live:=
        ((retagged.machine.memory.live.filter (fun row=>row.1 != physical.id)).push (physical.id,{physical.entry with allocation:=updated}))}}} ∧
      updated.extra=written.tree ∧ updated.byteSize=physical.entry.allocation.byteSize ∧ updated.len=physical.entry.allocation.len ∧
      updated.mutability=.Mut ∧ Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
        ((physical.entry.allocation.setExtra output.child.tree).setExtra written.tree)=.ok () updated ∧
      AllocationCopy.snapshot updated=AllocationCopy.snapshot physical.entry.allocation ∧
      retagged.machine.borrowTracker=some (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).extra.borrowTracker=
        some (borrowFrame.addProtector physical.id tracker.global.nextPointerTag) ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).returnPlace=frame.returnPlace ∧
      DuplicatePrefixRuntimeInput.State retagged.machine ⟨output.global,tracker.retagMode⟩ ∧
      written.status=.Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts written.tree output.global ∧
      ParentInterpretation written.tree (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) ∧
      GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority written.tree
        (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) output.global.protectedTags child)
        physical.offset (physical.offset+1) written.tree.locations ∧
      written.tree.nodes=output.child.tree.nodes ∧written.tree.roots=output.child.tree.roots ∧
      written.tree.tagMapping=output.child.tree.tagMapping ∧written.tree.locations.size=output.child.tree.locations.size ∧
      ∀(i : Fin source.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active source i)
        (byte : AllocId×Nat) (request : Window source.backing.id sourceOffset sourceLength byte)
        (cell : Window source.backing.id source.backing.cells[i].offset source.backing.cells[i].length byte),
        ∃(data : Identities) (Q : UniformWindow (afterMachine retagged physical updated) ⟨output.global,tracker.retagMode⟩ data 0 source.backing.id byte.2 1 .ret),
          Q.allocation=(if source.backing.id=ret.backing.id then updated else source.backing.allocation) ∧
          Q.pointer=source.family.at (source.roles i overlap).grant ∧
          Q.precise.completion=(if source.backing.id=ret.backing.id then
            S05ConcreteProtectedChildCompletion.extend source.backing.cells[i].completion child (ret.roles (returnIndex ret) (returnOverlap ret)).grant
            else source.backing.cells[i].completion) := by
  classical
  by_cases same : source.backing.id=ret.backing.id
  · obtain ⟨output,child,actual,tag,global,outputFrame,witness,updated,protect,extra,size,len,mutable,mutation,snapshot,tracked,frameTracked,returnPlace,ctorState,writeDone,writeRuntime,writeParents,writeOwned,writeNodes,writeRoots,writeTags,writeCapacity,sourceFrames⟩ :=
      activate_same options limits remaining span ctx machine tracker joint returnOffset ret sourceOffset sourceLength source same separate frames frame borrowFrame state highwater frameBorrow place physical physicalId physicalOffset pointer binding fresh short ghost race backend ready
    refine ⟨output,child,actual,tag,global,outputFrame,witness,updated,protect,extra,size,len,mutable,mutation,snapshot,tracked,frameTracked,returnPlace,ctorState,writeDone,writeRuntime,writeParents,writeOwned,writeNodes,writeRoots,writeTags,writeCapacity,?_⟩
    intro i overlap byte request cell
    obtain ⟨Q,allocationEq,pointerEq,preciseEq⟩ := sourceFrames i overlap byte request cell
    let R := reindex Q source.backing.id same.symm
    have fields := reindex_fields Q source.backing.id same.symm
    exact ⟨_,R,by simpa only [ite_eq_left same] using fields.1.trans allocationEq,fields.2.1.trans pointerEq,
      by simpa only [ite_eq_left same] using (congrArg PreciseAllocation.completion fields.2.2).trans preciseEq⟩
  · obtain ⟨output,child,actual,tag,global,outputFrame,witness,updated,protect,extra,size,len,mutable,mutation,snapshot,tracked,frameTracked,returnPlace,ctorState,writeDone,writeRuntime,writeParents,writeOwned,writeNodes,writeRoots,writeTags,writeCapacity,sourceFrames⟩ :=
      activate_other options limits remaining span ctx machine tracker joint returnOffset ret sourceOffset sourceLength source same frames frame borrowFrame state highwater frameBorrow place physical physicalId physicalOffset pointer binding fresh short ghost race backend ready
    refine ⟨output,child,actual,tag,global,outputFrame,witness,updated,protect,extra,size,len,mutable,mutation,snapshot,tracked,frameTracked,returnPlace,ctorState,writeDone,writeRuntime,writeParents,writeOwned,writeNodes,writeRoots,writeTags,writeCapacity,?_⟩
    intro i overlap byte request cell
    obtain ⟨Q,allocationEq,pointerEq,preciseEq⟩ := sourceFrames i overlap byte request cell
    exact ⟨_,Q,by simpa only [ite_eq_right same] using allocationEq,pointerEq,by simpa only [ite_eq_right same] using preciseEq⟩

end
end DuplicatePrefix.CurrentCallSpatialBoolActivation

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallSpatialBoolActivation.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial Bool activation dependency {dependency}"
