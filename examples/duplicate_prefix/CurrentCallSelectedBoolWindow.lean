import duplicate_prefix.CurrentCallSelectedBoolCurrent
import duplicate_prefix.CurrentCallResourceCopyInstall
namespace DuplicatePrefix.CurrentCallSelectedBoolWindow
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
open GeneralBorrowFnEntryRegistration GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
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


private theorem locations_frame (first second : BorrowTree)
    (nodes : second.nodes=first.nodes) (roots : second.roots=first.roots) (tags : second.tagMapping=first.tagMapping) :
    second={first with locations:=second.locations} := by
  cases first
  cases second
  simp_all

/-- Install the SAME protected Bool child in the actual written allocation.
Constructor and final presence are operation-internal witnesses; storage bytes
and provenance may change through the actual writeUninit. -/
theorem window {before tracker data owner id offset}
    (W : UniformWindow before tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (distinct : W.allocation.extra.roots.toList.Nodup) (room : W.allocation.extra.nodes.size+1<65536)
    (start : UInt64) (startEq : start.toNat=offset)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start 1=.ok output)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child start 1)
    (tag : output.tag=tracker.global.nextPointerTag)
    (constructor : Before) (constructorPresent : Present (ActualWorld constructor) id (W.allocation.setExtra output.child.tree))
    (rootTag : output.global.rootTag? id=tracker.global.rootTag? id)
    (post : Before) (updated : Allocation Provenance BorrowTree)
    (present : Present (ActualWorld post) id updated)
    (lengthEq : updated.len=W.allocation.len) (bytesEq : updated.byteSize=W.allocation.byteSize)
    (extra : updated.extra=(output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes start) (Size.ofBytes 1)
      .Write output.global.protectedTags .VisitChildrenOfAccessed).tree) :
    ∃ nextData nextOwner,∃ Q : UniformWindow post ⟨output.global,tracker.retagMode⟩ nextData nextOwner id offset 1 .ret,
      Q.pointer=CurrentCallResourceFnEntry.child_pointer W output.tag child ∧ Q.allocation=updated ∧
      Q.precise.completion=S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant ∧
      DuplicatePrefixBorrowContract.RuntimeFacts updated.extra output.global ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority updated.extra Q.precise.completion output.global.protectedTags child)
        start (start+1) updated.extra.locations ∧
      witness.node.children=#[] ∧ witness.node.isExposed=false ∧
      updated.extra.nodes.get child=some witness.node ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin updated.extra child .Write start (start+1) ∧
      SpatialDelegation post ⟨output.global,tracker.retagMode⟩ id updated Q.precise.completion W.pointer.grant ∧
      PointerBinds updated W.pointer := by
  obtain ⟨done,afterRuntime,parents,owned,nodes,roots,tags,capacity⟩ :=
    CurrentCallSelectedBoolCurrent.operation_runtime W runtime frame fresh distinct room start startEq output child actual witness tag
      constructor constructorPresent rootTag .VisitChildrenOfAccessed
  have updatedRuntime : DuplicatePrefixBorrowContract.RuntimeFacts updated.extra output.global := by rw [extra];exact afterRuntime
  have updatedParents : ParentInterpretation updated.extra (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) := by rw [extra];exact parents
  have updatedOwned : OwnedOn (S05CompletedAncestryReadMutable.Authority updated.extra
      (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) output.global.protectedTags child)
      start (start+1) updated.extra.locations := by rw [extra];exact owned
  have updatedNodes : updated.extra.nodes=output.child.tree.nodes := by rw [extra];exact nodes
  have updatedRoots : updated.extra.roots=output.child.tree.roots := by rw [extra];exact roots
  have updatedTags : updated.extra.tagMapping=output.child.tree.tagMapping := by rw [extra];exact tags
  have updatedCapacity : updated.extra.locations.size=output.child.tree.locations.size := by rw [extra];exact capacity
  have shape := locations_frame output.child.tree updated.extra updatedNodes updatedRoots updatedTags
  obtain ⟨parentIssued,childIssued⟩ := CurrentCallBorrowIssuance.post W runtime output child start 1 witness tag constructor
    ⟨output.global,tracker.retagMode⟩ constructorPresent rootTag
  let current := childView W output child start witness constructor constructorPresent childIssued
  have bounds : start.toNat+1≤output.child.tree.locations.size.bytes.toNat := by
    rw [witness.capacity,W.issued.capability.treeExtent,←W.issued.capability.extent]
    have bound := (W.window (id,offset) ⟨rfl,Nat.le_refl _,by omega⟩).1
    omega
  have noWrap : (start+1).toNat=start.toNat+1 := by rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt _))]
  obtain ⟨Q,loanQ,pointerQ,allocationQ,preciseQ⟩ := CurrentCallResourceCopyInstall.window current rfl post updated present
    lengthEq bytesEq shape updatedCapacity updatedRuntime updatedParents start 1 startEq rfl (by omega) noWrap updatedOwned
  have parentFinal : SpatialDelegation post ⟨output.global,tracker.retagMode⟩ id updated
      (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) W.pointer.grant := by
    apply CurrentCallAllocationLicense.spatial parentIssued post ⟨output.global,tracker.retagMode⟩ updated present rfl lengthEq bytesEq updatedCapacity
    · intro position root found;rw [updatedRoots];exact found
    · intro index node found;exact ⟨node,by rw [updatedNodes];exact found,rfl,rfl,rfl,rfl⟩
    · intro first second edge;exact edge
  have parentBinding : PointerBinds updated W.pointer := by
    obtain ⟨node,found,mapped,binding⟩ := W.binding
    obtain ⟨next,nextAt,nodeTag,_,exposure,_⟩ := witness.oldNodes W.pointer.grant node found
    refine ⟨next,by rw [updatedNodes];exact nextAt,updatedRuntime.formed.allocator.nodeTags _ _ (by rw [updatedNodes];exact nextAt),?_⟩
    cases provenance : W.pointer.value.provenance with
    | concrete supplied parentTag =>
      simp only [provenance] at binding ⊢
      exact ⟨binding.1,binding.2.trans nodeTag.symm⟩
    | wildcard =>
      simp only [provenance] at binding ⊢
      exact exposure.trans binding
  obtain ⟨leaf,hidden,active⟩ := CurrentCallSelectedBoolCurrent.facets W runtime frame fresh distinct room start startEq output child actual witness tag
  refine ⟨_,_,Q,pointerQ,allocationQ,?_,updatedRuntime,?_,leaf,hidden,?_,?_,?_,parentBinding⟩
  · rw [preciseQ];rfl
  · rw [preciseQ];exact updatedOwned
  · rw [updatedNodes];exact witness.nodeAt
  · rw [extra];exact active
  · rw [preciseQ];exact parentFinal

end
end DuplicatePrefix.CurrentCallSelectedBoolWindow
