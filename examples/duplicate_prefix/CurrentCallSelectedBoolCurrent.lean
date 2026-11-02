import duplicate_prefix.S03ReturnChildMetadata
import duplicate_prefix.GeneralBorrowConstructorChildActivity
import duplicate_prefix.GeneralBorrowWildcardRootConstructorActivity
import duplicate_prefix.GeneralBorrowFreshActiveWithinAccess
import duplicate_prefix.CurrentCallBoolWriteRuntime
import duplicate_prefix.CurrentCallBoolActivationOperation
import duplicate_prefix.CurrentCallResourceChildWrite
import duplicate_prefix.CurrentCallResourceBorrowGrowth

/-! One actual Bool protection from its selected current runtime and resource.
No whole-machine post-state or future operation outcome is an input. -/
namespace DuplicatePrefix.CurrentCallSelectedBoolCurrent
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

theorem write_runtime {before tracker data owner id offset}
    (W : UniformWindow before tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex) (start : UInt64)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child start 1)
    (tag : output.tag = tracker.global.nextPointerTag)
    (post : Before) (present : Present (ActualWorld post) id (W.allocation.setExtra output.child.tree))
    (rootTag : output.global.rootTag? id = tracker.global.rootTag? id)
    (distinct : output.child.tree.roots.toList.Nodup) (short : output.child.tree.nodes.size < 65536)
    (startEq : start.toNat = offset)     (bounds : start.toNat+1 ≤ output.child.tree.locations.size.bytes.toNat)
    (visit : ChildrenVisitMode) :
    let result := output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes start) (Size.ofBytes 1)
      .Write output.global.protectedTags visit
    result.status = .Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts result.tree output.global ∧
    ParentInterpretation result.tree (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) ∧
    GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority result.tree
        (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) output.global.protectedTags child)
      start (start+1) result.tree.locations ∧
    result.tree.nodes = output.child.tree.nodes ∧ result.tree.roots = output.child.tree.roots ∧
    result.tree.tagMapping = output.child.tree.tagMapping ∧ result.tree.locations.size = output.child.tree.locations.size := by
  let result := output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes start) (Size.ofBytes 1)
    .Write output.global.protectedTags visit
  have issued := (CurrentCallBorrowIssuance.post W runtime output child start 1 witness tag post
    ⟨output.global,tracker.retagMode⟩ present rootTag).2
  let current := childView W output child start witness post present issued
  obtain ⟨geometry⟩ := geometry_selected current (CandidateCurrentGrantRuntime.tree_rows output.child.tree output.global witness.runtime) (by rfl)
  have noWrap : start.toNat+1<2^64 := Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt _)
  have endEq : (start+1).toNat=start.toNat+1 := by rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt noWrap]
  have contract := CurrentCallResourceAccess.write_range current geometry (by rfl) distinct short witness.runtime.formed.well
    (fun position valid=>⟨witness.runtime.coherent position valid,witness.runtime.formed.profile position valid,witness.runtime.possible position valid⟩)
    (Size.ofBytes start) (Size.ofBytes 1) start (start+1)
    (by omega) (by omega) bounds (Nat.le_refl _) (Nat.le_refl _) visit
  dsimp only [current,childView,CurrentCallResourceFnEntry.child_pointer,Allocation.setExtra,Allocation.mapExtra] at contract
  have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts result.tree output.global := by
    rw [contract.tree_eq]
    refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations output.child.tree _ witness.runtime.formed.toGraphState,contract.well⟩,?_⟩,
      ?_,?_,⟨witness.runtime.below.mapping,witness.runtime.below.protectors⟩⟩
    · intro cursor valid
      exact ⟨(contract.runtime cursor valid).2.1.present,(contract.runtime cursor valid).2.1.vacant⟩
    · intro cursor valid
      exact (contract.runtime cursor valid).1
    · intro cursor valid
      exact (contract.runtime cursor valid).2.2
  have parents : ParentInterpretation result.tree
      (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) := by
    rw [contract.tree_eq]
    refine ⟨GeneralBorrowStructuralHistoryState.graph_locations output.child.tree _ witness.parents.graph,
      witness.parents.order,witness.parents.dimension,witness.parents.physical,witness.parents.edgeLive,witness.parents.primaryNone,?_⟩
    intro position root slot origin edge
    obtain ⟨earlier,originRoot,rootNode,originNode,before,rootSlot,rootAt,originAt,exposed,older,path⟩ := witness.parents.virtual position root slot origin edge
    exact ⟨earlier,originRoot,rootNode,originNode,before,rootSlot,rootAt,originAt,exposed,older,
      GeneralBorrowPrimaryWitnessVisibility.path_nodes (before := {output.child.tree with locations := result.tree.locations})
        (after := output.child.tree) rfl path⟩
  refine ⟨contract.completed,afterRuntime,parents,?_,contract.nodes,contract.roots,contract.tags,contract.capacity⟩
  intro cursor valid positive start stop index node found
  exact contract.rows cursor valid positive start stop index node (by rw [←contract.nodes];exact found)


/-- Recover the SAME child's actual Write from selected current resources.
All post-constructor headroom is derived from the actual operation. -/
theorem operation_runtime {before tracker data owner id offset}
    (W : UniformWindow before tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (distinct : W.allocation.extra.roots.toList.Nodup)
    (room : W.allocation.extra.nodes.size+1<65536)
    (start : UInt64) (startEq : start.toNat=offset)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start 1=.ok output)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child start 1)
    (tag : output.tag=tracker.global.nextPointerTag)
    (post : Before) (present : Present (ActualWorld post) id (W.allocation.setExtra output.child.tree))
    (rootTag : output.global.rootTag? id=tracker.global.rootTag? id)
    (visit : ChildrenVisitMode) :
    let result := output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes start) (Size.ofBytes 1)
      .Write output.global.protectedTags visit
    result.status = .Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts result.tree output.global ∧
    ParentInterpretation result.tree (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) ∧
    GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority result.tree
        (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) output.global.protectedTags child)
      start (start+1) result.tree.locations ∧
    result.tree.nodes = output.child.tree.nodes ∧ result.tree.roots = output.child.tree.roots ∧
    result.tree.tagMapping = output.child.tree.tagMapping ∧ result.tree.locations.size = output.child.tree.locations.size := by
  have bounds : start.toNat+1≤W.allocation.extra.locations.size.bytes.toNat := by
    have bound := (W.window (id,offset) ⟨rfl,Nat.le_refl _,by omega⟩).1
    rw [W.issued.capability.treeExtent,←W.issued.capability.extent]
    omega
  have oldShort : W.allocation.extra.nodes.size<65536 := by omega
  have nodeRoom : W.allocation.extra.nodes.size+1≤4294967295 := by omega
  have afterDistinct := roots W runtime frame fresh rfl distinct oldShort nodeRoom start 1 startEq rfl (by decide) bounds output actual
  have afterGrowth := growth W runtime frame fresh rfl distinct oldShort nodeRoom start 1 startEq rfl (by decide) bounds output actual
  exact write_runtime W runtime output child start witness tag post present rootTag afterDistinct (by omega) startEq (by rw [witness.capacity];exact bounds) visit

private theorem selected_facets {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (exclusive : demandOf mode=.exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size<65536) (nodeRoom : W.allocation.extra.nodes.size+1≤4294967295)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length) (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤W.allocation.extra.locations.size.bytes.toNat)
    (output : GeneralBorrowForestFnEntry.Output)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount=.ok output) :
    DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree (registered tracker.global frame id room).1 ∧
    output.child.tree.locations.size=W.allocation.extra.locations.size ∧
    ∃ child node, output.child.tree.indexOfTag tracker.global.nextPointerTag=some child ∧
      output.child.tree.nodeAt child=some node ∧ node.tag=tracker.global.nextPointerTag ∧
      node.children=#[] ∧ node.isExposed=false ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write start (start+amount) := by
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
    obtain ⟨child,node,lookup,present,nodeTag,parent,leaf,hidden,old⟩ := S03ReturnChildMetadata.construct output.access.tree registration.1 afterRuntime parentTag tracker.global.nextPointerTag W.pointer.grant parentNode tagged parentAfter freshAfter nodeCapacity start amount nonzero childBounds
    obtain ⟨activeChild,activeLookup,active⟩ := GeneralBorrowConstructorChildActivity.Protected.construct output.access.tree registration.1 afterRuntime parentTag tracker.global.nextPointerTag W.pointer.grant parentNode tagged parentAfter freshAfter nodeCapacity start amount nonzero childBounds
    have eqChild : activeChild=child := Option.some.inj (activeLookup.symm.trans lookup)
    subst activeChild
    rw [childEq]
    simpa only [prov,CandidateCurrentWindowPointerChecks.extraOf] using
      And.intro ctor.2.1 (And.intro (ctor.2.2.1.trans bytes) ⟨child,node,lookup,present,nodeTag,leaf,hidden,active⟩)

  | wildcard =>
    have ctor := GeneralBorrowWildcardConstructorRuntime.protected_mutable output.access.tree registration.1 afterRuntime tracker.global.nextPointerTag freshAfter nodeCapacity tagBound tagHeld
      start amount nonzero childBounds
    obtain ⟨mapping,index,inserted,rows,vacant,graph,monotone,growth⟩ := GeneralBorrowWildcardConstructorSlot.select output.access.tree registration.1 afterRuntime tracker.global.nextPointerTag freshAfter nodeCapacity (.ReservedFrz false) .None
    have exactTree := GeneralBorrowWildcardConstructorExact.exact output.access.tree afterRuntime.formed.toState tracker.global.nextPointerTag freshAfter nodeCapacity mapping index inserted
      (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl start amount nonzero childBounds
    have present : (GeneralBorrowPositiveWildcardConstructor.result output.access.tree mapping index tracker.global.nextPointerTag (.ReservedFrz false) .None GeneralBorrowFreshChild.inside start amount).nodeAt index = some (WildcardHitZeroConstructor.rootNode tracker.global.nextPointerTag (.ReservedFrz false) .None) := GeneralBorrowFreshLocation.get_same output.access.tree.nodes index _
    have lookup := graph.allocator.nodeTags index _ present
    obtain ⟨activeChild,activeLookup,active⟩ := GeneralBorrowWildcardRootConstructorActivity.construct output.access.tree registration.1 afterRuntime tracker.global.nextPointerTag freshAfter nodeCapacity start amount nonzero childBounds
    rw [exactTree] at activeLookup active
    have eqChild : activeChild=index := Option.some.inj (activeLookup.symm.trans lookup)
    subst activeChild
    rw [childEq]
    simp only [prov,CandidateCurrentWindowPointerChecks.extraOf]
    refine ⟨ctor.2.1,ctor.2.2.1.trans bytes,?_⟩
    rw [exactTree]
    exact ⟨index,_,lookup,present,rfl,rfl,rfl,active⟩

theorem facets {before tracker data owner id offset}
    (W : UniformWindow before tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (distinct : W.allocation.extra.roots.toList.Nodup)
    (room : W.allocation.extra.nodes.size+1<65536)
    (start : UInt64) (startEq : start.toNat=offset)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start 1=.ok output)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child start 1)
    (tag : output.tag=tracker.global.nextPointerTag)
 :
    witness.node.children=#[] ∧ witness.node.isExposed=false ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin
      (output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes start) (Size.ofBytes 1)
        .Write output.global.protectedTags .VisitChildrenOfAccessed).tree child .Write start (start+1) := by
  have bounds : start.toNat+1≤W.allocation.extra.locations.size.bytes.toNat := by
    have bound := (W.window (id,offset) ⟨rfl,Nat.le_refl _,by omega⟩).1
    rw [W.issued.capability.treeExtent,←W.issued.capability.extent]
    omega
  obtain ⟨afterRuntime,capacity,index,node,lookup,present,nodeTag,leaf,hidden,active⟩ := selected_facets W runtime frame fresh rfl distinct
    (by omega) (by omega) start 1 startEq rfl (by decide) bounds output actual
  have ownLookup : output.child.tree.indexOfTag tracker.global.nextPointerTag=some child := by
    rw [←tag,←witness.tag]
    exact witness.runtime.formed.allocator.nodeTags _ _ witness.nodeAt
  have childEq : index=child:=Option.some.inj (lookup.symm.trans ownLookup)
  subst index
  have nodeEq : node=witness.node:=Option.some.inj (present.symm.trans witness.nodeAt)
  subst node
  refine ⟨leaf,hidden,?_⟩
  rw [tag]
  exact GeneralBorrowFreshActiveWithinAccess.normal output.child.tree tracker.global.nextPointerTag
    (Size.ofBytes start) (Size.ofBytes 1) .Write output.global.protectedTags .VisitChildrenOfAccessed child start (start+1)
    afterRuntime.formed.well (by rw [capacity];exact bounds) (Nat.le_refl _) (Nat.le_refl _) active

end
end DuplicatePrefix.CurrentCallSelectedBoolCurrent
