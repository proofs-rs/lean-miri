import duplicate_prefix.CurrentCallBoolActivationOperation
import duplicate_prefix.CurrentCallResourceChildWrite
import duplicate_prefix.CurrentCallResourceBorrowGrowth

/-! One actual Bool protection from its selected current runtime and resource.
No whole-machine post-state or future operation outcome is an input. -/
namespace DuplicatePrefix.CurrentCallSelectedBoolProtection
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
open GeneralBorrowFnEntryRegistration TypedBorrowSteps ReferenceBorrowDriver ReturnProtection
open CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
private def extra (provenance : Provenance) : ProvenanceExtra :=
  match provenance with | .concrete _ tag=>.concrete tag | .wildcard=>.wildcard
private theorem child_of_operation (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (id : AllocId) (provenance : Provenance) (start amount : UInt64)
    (room : global.nextPointerTag.value < 18446744073709551615) (output : GeneralBorrowForestFnEntry.Output)
    (actual : CandidateCurrentFnEntryRaw.operation tree global frame id provenance start amount = .ok output) :
    output.child =
      (tree.performBorrowAccessRange (extra provenance)
        (Size.ofBytes start) (Size.ofBytes amount) .Read (registered global frame id room).1.protectedTags .VisitChildrenOfAccessed).tree.newChild
      (Size.ofBytes start) (extra provenance) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true := by
  have allocated := TypedRetagEmpty.allocate_tag global room
  cases provenance with
  | concrete suppliedId tag =>
    simp only [CandidateCurrentFnEntryRaw.operation,GeneralBorrowForestFnEntry.operation,GeneralBorrowForestProtected.read,
      allocated,Except.bind,Except.pure,bind,pure] at actual
    cases Except.ok.inj actual
    rfl
  | wildcard =>
    simp only [CandidateCurrentFnEntryRaw.operation,GeneralBorrowRawWildcardFnEntryRuntime.operation,
      allocated,Except.bind,Except.pure,bind,pure] at actual
    cases Except.ok.inj actual
    rfl

private theorem roots {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (exclusive : demandOf mode=.exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size<65536) (nodeRoom : W.allocation.extra.nodes.size+1≤4294967295)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length) (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤W.allocation.extra.locations.size.bytes.toNat)
    (output : GeneralBorrowForestFnEntry.Output)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount=.ok output) :
    output.child.tree.roots.toList.Nodup := by
  obtain ⟨_,_,_,_,_,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare W.allocation.extra tracker.global frame id room runtime
  let registration := registered tracker.global frame id room
  let accessed := W.allocation.extra.performBorrowAccessRange (extra W.pointer.value.provenance)
    (Size.ofBytes start) (Size.ofBytes amount) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨_,afterRuntime,_,_,nodes,rootFrame,tags,capacity⟩ := CurrentCallResourceFnEntry.prepare_read_selected W runtime frame room exclusive distinct short start amount startEq amountEq bounds
  change DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree registration.1 at afterRuntime
  change accessed.tree.nodes=W.allocation.extra.nodes at nodes
  change accessed.tree.roots=W.allocation.extra.roots at rootFrame
  change accessed.tree.tagMapping=W.allocation.extra.tagMapping at tags
  change accessed.tree.locations.size=W.allocation.extra.locations.size at capacity
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [tags];exact fresh
  have afterRoom : accessed.tree.nodes.size+1≤4294967295 := by rw [nodes];exact nodeRoom
  have afterBounds : start.toNat+amount.toNat≤accessed.tree.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have childEq := child_of_operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount room output actual
  cases provenance : W.pointer.value.provenance with
  | concrete suppliedId parentTag =>
    obtain ⟨parentNode,parentAt,_,binds⟩ := W.binding
    rw [provenance] at binds
    have parentAfter : accessed.tree.nodeAt W.pointer.grant=some parentNode := by change accessed.tree.nodes.get _=_;rw [nodes];exact parentAt
    have tagged : accessed.tree.indexOfTag parentTag=some W.pointer.grant := by rw [binds.2];exact afterRuntime.formed.allocator.nodeTags _ _ parentAfter
    let depth := GeneralBorrowStructuralHistoryMutable.depth accessed.tree afterRuntime.formed.toState
    let slot := GeneralBorrowStructuralHistoryMutable.slot accessed.tree afterRuntime.formed.toState W.pointer.grant parentNode parentAfter afterRoom
    have metadata := GeneralBorrowFreshMetadataChildMutableSlot.build accessed.tree depth afterRuntime.formed.children afterRuntime.formed.covered
      parentTag tracker.global.nextPointerTag W.pointer.grant parentNode tagged parentAfter freshAfter slot start amount nonzero
      afterRuntime.formed.well afterRuntime.formed.fits afterBounds
    rw [childEq]
    have rootEq := metadata.roots
    rw [rootFrame] at rootEq
    have unique : (GeneralBorrowFreshMetadataChildMutableSlot.result accessed.tree parentTag tracker.global.nextPointerTag start amount).roots.toList.Nodup := by rw [rootEq];exact distinct
    simpa only [GeneralBorrowFreshMetadataChildMutableSlot.result,accessed,registration,provenance,extra] using unique
  | wildcard =>
    obtain ⟨mapping,index,inserted,_,vacant,_,_,_⟩ := GeneralBorrowWildcardConstructorSlot.select accessed.tree registration.1 afterRuntime
      tracker.global.nextPointerTag freshAfter afterRoom (.ReservedFrz false) .None
    have exactCtor := GeneralBorrowWildcardConstructorExact.exact accessed.tree afterRuntime.formed.toState tracker.global.nextPointerTag freshAfter afterRoom mapping index inserted
      (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl start amount nonzero afterBounds
    have outside : index∉accessed.tree.roots.toList := by
      intro member
      obtain ⟨node,present,_⟩ := afterRuntime.formed.rootNodes index member
      rw [vacant] at present
      contradiction
    have unique : accessed.tree.roots.toList.Nodup := by rw [rootFrame];exact distinct
    have appended : (accessed.tree.roots.push index).toList.Nodup := by
      rw [Array.toList_push]
      apply List.nodup_append.mpr
      refine ⟨unique,by simp,?_⟩
      intro query member other single equal
      have same : other=index := by simpa using single
      subst other
      subst query
      exact outside member
    rw [childEq]
    simp only [provenance,extra]
    simp only [accessed,registration,provenance,extra] at exactCtor
    rw [exactCtor]
    simpa only [GeneralBorrowPositiveWildcardConstructor.result,WildcardHitZeroConstructor.installed,accessed,registration,provenance,extra] using appended


private theorem growth {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (exclusive : demandOf mode=.exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size<65536) (nodeRoom : W.allocation.extra.nodes.size+1≤4294967295)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length) (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤W.allocation.extra.locations.size.bytes.toNat)
    (output : GeneralBorrowForestFnEntry.Output)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount=.ok output) :
    output.child.tree.nodes.size ≤ W.allocation.extra.nodes.size + 1 := by
  have literalEq : output=CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount := by
    exact Except.ok.inj (actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ room _ _ _))
  obtain ⟨_,held,_,_,_,freshTag⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare W.allocation.extra tracker.global frame id room runtime
  let registration := registered tracker.global frame id room
  obtain ⟨_,afterRuntime,_,_,nodes,_,tags,bytes⟩ := CurrentCallResourceFnEntry.prepare_read_selected W runtime frame room exclusive
    distinct short start amount startEq amountEq bounds
  change DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount).access.tree registration.1 at afterRuntime
  rw [←literalEq] at afterRuntime
  change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount).access.tree.nodes=W.allocation.extra.nodes at nodes
  change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount).access.tree.tagMapping=W.allocation.extra.tagMapping at tags
  change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount).access.tree.locations.size=W.allocation.extra.locations.size at bytes
  rw [←literalEq] at nodes tags bytes
  have freshAfter : GeneralBorrowTagMap.Fresh output.access.tree.tagMapping tracker.global.nextPointerTag := by rw [tags];exact freshTag
  have nodeCapacity : output.access.tree.nodes.size+1≤4294967295 := by rw [nodes];exact nodeRoom
  have childBounds : start.toNat+amount.toNat≤output.access.tree.locations.size.bytes.toNat := by rw [bytes];exact bounds
  have tagBound : tracker.global.nextPointerTag.value.toNat<registration.1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have tagHeld : registration.1.protectedTags.contains tracker.global.nextPointerTag=true := by unfold ProtectedTags.contains;rw [held];rfl
  have childEq : output.child=output.access.tree.newChild (Size.ofBytes start) (CandidateCurrentWindowPointerChecks.extraOf W.pointer.value.provenance)
    tracker.global.nextPointerTag (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true := by rw [literalEq];rfl
  cases prov : W.pointer.value.provenance with
  | concrete id parentTag =>
    obtain ⟨parentNode,parentAt,_,binds⟩ := W.binding
    rw [prov] at binds
    have parentAfter : output.access.tree.nodeAt W.pointer.grant=some parentNode := by change output.access.tree.nodes.get _=_;rw [nodes];exact parentAt
    have tagged : output.access.tree.indexOfTag parentTag=some W.pointer.grant := by rw [binds.2];exact afterRuntime.formed.allocator.nodeTags _ _ parentAfter
    have ctor := GeneralBorrowProtectedConstructorRuntime.construct output.access.tree registration.1 afterRuntime parentTag tracker.global.nextPointerTag W.pointer.grant parentNode
      tagged parentAfter freshAfter nodeCapacity tagBound tagHeld start amount nonzero childBounds
    rw [childEq]
    simpa only [prov,CandidateCurrentWindowPointerChecks.extraOf,nodes] using ctor.2.2.2
  | wildcard =>
    have ctor := GeneralBorrowWildcardConstructorRuntime.protected_mutable output.access.tree registration.1 afterRuntime tracker.global.nextPointerTag freshAfter nodeCapacity tagBound tagHeld
      start amount nonzero childBounds
    rw [childEq]
    simpa only [prov,CandidateCurrentWindowPointerChecks.extraOf,nodes] using ctor.2.2.2.1


private def childData {before tracker data owner id offset}
    (W : UniformWindow before tracker data owner id offset 1 .ret)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex) : Identities :=
  ⟨⟨#[(id,{W.precise with completion:=S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant})],
    #[CurrentCallResourceFnEntry.child_pointer W output.tag child],#[⟨0,none,0⟩],fun _ _=>none⟩,#[],#[]⟩

private def childView {before tracker data owner id offset}
    (W : UniformWindow before tracker data owner id offset 1 .ret)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex) (start : UInt64)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child start 1)
    (post : Before)
    (present : Present (ActualWorld post) id (W.allocation.setExtra output.child.tree))
    (issued : SpatialDelegation post ⟨output.global,tracker.retagMode⟩ id (W.allocation.setExtra output.child.tree)
      (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) child) :
    UniformWindow post ⟨output.global,tracker.retagMode⟩ (childData W output child) 0 id offset 1 .ret where
  loan := ⟨0,none,0⟩
  pointer := CurrentCallResourceFnEntry.child_pointer W output.tag child
  allocation := W.allocation.setExtra output.child.tree
  precise := {W.precise with completion:=S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant}
  loanAt := by simp [childData]
  pointerAt := by simp [childData]
  pointerId := rfl
  present := present
  preciseAt := by simp [childData]
  binding := witness.binding
  issued := issued
  parents := witness.parents
  window := by
    intro byte inside
    obtain ⟨bound,embedding⟩ := witness.window byte inside
    refine ⟨?_,?_⟩
    · simpa only [Allocation.len,Allocation.setExtra,Allocation.mapExtra] using bound
    · simpa [demandOf,CurrentCallResourceFnEntry.child_pointer] using embedding

/-- Physical storage readiness and current Bool ownership derive the literal
retag/protected-child Write and actual byte clearing. Only the selected tree's
runtime is required; no full State after source copying or clearing is assumed. -/
theorem protect (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (machine : Before) (tracker : MachineHooks.BorrowState) (data : Identities) (owner : Nat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (enabled : machine.borrowTracker=some tracker) (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place)
    (W : UniformWindow machine tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer=W.pointer.value) (allocation : physical.entry.allocation=W.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1)
    (distinct : W.allocation.extra.roots.toList.Nodup)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (short : W.allocation.extra.nodes.size+1<65536)
    (ghost : machine.user.payload.ghost=false) (race : machine.dataRace=none) (backend : machine.user.payload.payload.user.backend=.none)
    (ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1) :
    ∃(output : GeneralBorrowForestFnEntry.Output) (child : UniIndex),
      CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global borrowFrame physical.id W.pointer.value.provenance physical.offset 1=.ok output ∧
      output.tag=tracker.global.nextPointerTag ∧ output.global=(registered tracker.global borrowFrame physical.id fresh).1 ∧
      output.frame=(registered tracker.global borrowFrame physical.id fresh).2 ∧
      Nonempty (CurrentCallResourceFnEntry.BorrowWitness W output child physical.offset 1) ∧
    let retagged := borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry output.child.tree
    let written := output.child.tree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
      .Write (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed
    ∃ updated,(ExecutionMachine.callHooks (config options remaining span) limits).protectArgument () place
      (Storage.withCurrent frames frame machine)=
      .ok () {retagged with machine:={retagged.machine with memory:={retagged.machine.memory with live:=
        ((retagged.machine.memory.live.filter (fun row=>row.1!=physical.id)).push (physical.id,{physical.entry with allocation:=updated}))}}} ∧
      updated.extra=written.tree ∧ updated.byteSize=physical.entry.allocation.byteSize ∧ updated.len=physical.entry.allocation.len ∧
      updated.mutability=.Mut ∧ Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
        ((physical.entry.allocation.setExtra output.child.tree).setExtra written.tree)=.ok () updated ∧
      AllocationCopy.snapshot updated=AllocationCopy.snapshot physical.entry.allocation ∧
      retagged.machine.borrowTracker=some (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).extra.borrowTracker=
        some (borrowFrame.addProtector physical.id tracker.global.nextPointerTag) ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).returnPlace=frame.returnPlace := by
  have bounds : physical.offset.toNat+1≤W.allocation.extra.locations.size.bytes.toNat := by
    have bound := (W.window (physical.id,physical.offset.toNat) ⟨rfl,Nat.le_refl _,by omega⟩).1
    rw [W.issued.capability.treeExtent,←W.issued.capability.extent]
    omega
  have oldShort : W.allocation.extra.nodes.size<65536 := by omega
  have nodeRoom : W.allocation.extra.nodes.size+1≤4294967295 := by omega
  obtain ⟨output,child,actual,tag,global,frameEq,readDone,childDone,lookup,⟨witness⟩⟩ :=
    CurrentCallResourceFnEntry.correlated_borrow_selected W runtime borrowFrame fresh (by rfl) distinct oldShort nodeRoom
      physical.offset 1 rfl rfl (by decide) bounds
  let retagged := borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry output.child.tree
  have present : Present (ActualWorld retagged.machine) physical.id (W.allocation.setExtra output.child.tree) := by
    simp only [Present,ActualWorld,Array.toList_map]
    apply List.mem_map.mpr
    refine ⟨(physical.id,{physical.entry with allocation:=physical.entry.allocation.setExtra output.child.tree}),?_,?_⟩
    · exact Array.mem_toList_iff.mpr (Array.mem_push.mpr (.inr rfl))
    · simp only [allocation]
  have rootTag : output.global.rootTag? physical.id=tracker.global.rootTag? physical.id := by rw [global];rfl
  have issued := (CurrentCallBorrowIssuance.post W runtime output child physical.offset 1 witness tag retagged.machine
    ⟨output.global,tracker.retagMode⟩ present rootTag).2
  let current := childView W output child physical.offset witness retagged.machine present issued
  obtain ⟨geometry⟩ := geometry_selected current (CandidateCurrentGrantRuntime.tree_rows output.child.tree output.global witness.runtime) (by rfl)
  have afterDistinct := roots W runtime borrowFrame fresh (by rfl) distinct oldShort nodeRoom physical.offset 1 rfl rfl (by decide) bounds output actual
  have afterGrowth := growth W runtime borrowFrame fresh (by rfl) distinct oldShort nodeRoom physical.offset 1 rfl rfl (by decide) bounds output actual
  have afterBounds : physical.offset.toNat+1≤output.child.tree.locations.size.bytes.toNat := by rw [witness.capacity];exact bounds
  have noWrap : physical.offset.toNat+1<2^64 := Nat.lt_of_le_of_lt afterBounds (UInt64.toNat_lt _)
  have endEq : (physical.offset+1).toNat=physical.offset.toNat+1 := by rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt noWrap]
  have contract := CurrentCallResourceAccess.write_range current geometry (by rfl) afterDistinct (by change output.child.tree.nodes.size<65536;omega) witness.runtime.formed.well
    (fun position valid=>⟨witness.runtime.coherent position valid,witness.runtime.formed.profile position valid,witness.runtime.possible position valid⟩)
    (Size.ofBytes physical.offset) (Size.ofBytes 1) physical.offset (physical.offset+1)
    (Nat.le_refl _) (by omega) afterBounds (Nat.le_refl _) (Nat.le_refl _) .VisitChildrenOfAccessed
  have writeDone : (output.child.tree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
      .Write (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).status=.Completed := by
    have completed := contract.completed
    change (output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
      .Write output.global.protectedTags .VisitChildrenOfAccessed).status=.Completed at completed
    rw [tag,global] at completed
    exact completed
  have actualPhysical : CandidateCurrentFnEntryRaw.operation physical.entry.allocation.extra tracker.global borrowFrame
      physical.id physical.pointer.provenance physical.offset 1=.ok output := by rw [allocation,pointer];exact actual
  refine ⟨output,child,actual,tag,global,frameEq,⟨witness⟩,?_⟩
  exact CurrentCallBoolActivation.protect_of_operation options limits remaining span ctx machine tracker frames frame borrowFrame enabled frameBorrow
    place physical binding fresh ghost race backend output actualPhysical readDone childDone ready writeDone

end
end DuplicatePrefix.CurrentCallSelectedBoolProtection
