import duplicate_prefix.CurrentCallResourceSharedBoolFrame
import duplicate_prefix.CurrentCallResourceLenReturn
import duplicate_prefix.CurrentCallOptionalLenBoolFrame

namespace DuplicatePrefix.CurrentCallResourceLenBoolFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallResourceEntryBody GeneralBorrowFnEntryRegistration GeneralBorrowRawSharedExpression
open GeneralBorrowExposedNonleafPrimaryPath GeneralRangeMapOrigins
open CanonicalConfigFacts ActualReferenceContext LenUncachedFrontend GeneralBorrowForestMixedLenBeforeReturn
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true


private theorem untouched (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (target : UniIndex) (allocation : AllocId)
    (room : global.nextPointerTag.value<18446744073709551615)
    (fresh : ∀ index node,tree.nodes.get index=some node → node.tag≠global.nextPointerTag)
    (lower upper : UInt64)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags target)
      lower upper tree.locations) :
    let reg:=registered global {} allocation room
    OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion
      (reg.1.endCall reg.2).protectedTags target) lower upper tree.locations := by
  dsimp only
  intro cursor valid positive start stop index node present
  have other:=fresh index node present
  have inserted : (registered global {} allocation room).1.protectedTags.contains node.tag=global.protectedTags.contains node.tag :=
    ProtectorInsertion.contains_other global.protectedTags global.nextPointerTag node.tag .StrongProtector other
  have removed : ((registered global {} allocation room).1.endCall
      (registered global {} allocation room).2).protectedTags.contains node.tag=
      (registered global {} allocation room).1.protectedTags.contains node.tag := by
    change (((registered global {} allocation room).1.protectedTags).remove global.nextPointerTag).contains node.tag=_
    unfold ProtectedTags.contains
    rw [GeneralBorrowProtectorCacheMap.remove_other _ _ _ other]
  rw [removed,inserted]
  exact owned cursor valid positive start stop index node present

variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    (out : Output limits C count) (ready : CurrentCallResourceBodyReadiness.Ready C)

private theorem bool_tag_before_shared : out.boolNode.tag≠out.boolOutput.global.nextPointerTag := by
  have successor:=GenericFunctionEntryNumerics.successor_value out.sourceOutput.global.nextPointerTag out.returnRoom
  intro same
  have equal:=congrArg (fun tag : BorTag=>tag.value.toNat) same
  rw [out.boolNodeTag,out.boolTag,out.boolGlobal] at equal
  change out.sourceOutput.global.nextPointerTag.value.toNat=
    (TypedRetagEmpty.successorTag out.sourceOutput.global.nextPointerTag out.returnRoom).value.toNat at equal
  omega

/-- The original joint claims supply the actual source/Bool byte separation,
even when both windows belong to the same allocation. -/
theorem same_range (sameId : out.physical.id=id) :
    (UInt64.ofNat offset+len).toNat≤out.physical.offset.toNat ∨
      (out.physical.offset+1).toNat≤(UInt64.ofNat offset).toNat := by
  have bounds:=CurrentCallResourceSharedStage.source_bounds out
  have fits : offset<2^64 := by
    have positive:=C.positive
    have last := (W.window (id,offset+len.toNat-1) ⟨rfl,by omega,by omega⟩).1
    have extent:=W.issued.capability.extent
    have bounded:=UInt64.toNat_lt W.allocation.byteSize.bytes
    omega
  have startEq : (UInt64.ofNat offset).toNat=offset := by
    simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt fits]
  have endFits : (UInt64.ofNat offset).toNat+len.toNat<2^64 :=
    Nat.lt_of_le_of_lt bounds.2 (UInt64.toNat_lt _)
  have endEq : (UInt64.ofNat offset+len).toNat=offset+len.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt endFits,startEq]
  rw [startEq,endEq]
  by_cases left : offset+len.toNat≤out.physical.offset.toNat
  · exact Or.inl left
  apply Or.inr
  by_cases right : (out.physical.offset+1).toNat≤offset
  · exact right
  apply False.elim
  have offsetBound : out.physical.offset.toNat<offset+len.toNat := by omega
  let overlap := max offset out.physical.offset.toNat
  have source : Window id offset len.toNat (id,overlap) :=
    ⟨rfl,by dsimp [overlap];omega,by dsimp [overlap];have p:=C.positive;omega⟩
  have target : Window C.physical.id C.physical.offset.toNat 1 (id,overlap) := by
    refine ⟨(out.physicalId.symm.trans sameId).symm,?_,?_⟩
    · dsimp [overlap];rw [←out.physicalOffset];omega
    · dsimp [overlap];rw [←out.physicalOffset]
      have modBound : (out.physical.offset+1).toNat≤out.physical.offset.toNat+1 := by
        rw [UInt64.toNat_add];exact Nat.mod_le _ _
      omega
  exact C.separate (out.physicalId.symm.trans sameId) (id,overlap) source target


theorem same_of_preStrong {nextData nextOwner}
    (Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut)
    (pointer : Q.pointer=CurrentCallResourceSourceAfterBool.pointer out)
    (allocation : Q.allocation=(CurrentCallResourceSourceFinal.entry out).allocation)
    (completion : Q.precise.completion=CurrentCallResourceSourceFinal.completion out)
    (sameId : out.physical.id=id)
    (stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len
      (CurrentCallResourceBodyReadiness.current_room out ready))
    (P : CurrentCallResourceLenReturn.PreStrong out ready Q stage) :
    ∃ helper,
      (CurrentCallResourceLenInvoke.borrowedTree out ready).indexOfTag
        (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag=some helper ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority (CurrentCallResourceLenReturn.releasedTree out ready)
        (S05ConcreteProtectedChildCompletion.extend
          (S05ConcreteProtectedChildCompletion.extend Q.precise.completion stage.reader Q.pointer.grant) helper stage.reader)
        (CurrentCallResourceLenReturn.postTracker out ready).global.protectedTags out.boolChild)
        out.physical.offset (out.physical.offset+1) (CurrentCallResourceLenReturn.releasedTree out ready).locations ∧
      (∃ node,(CurrentCallResourceLenReturn.releasedTree out ready).nodeAt out.boolChild=some node ∧
        node.tag=out.boolNode.tag ∧ node.parent=out.boolNode.parent ∧ node.children=out.boolNode.children ∧ node.isExposed=out.boolNode.isExposed) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin (CurrentCallResourceLenReturn.releasedTree out ready) out.boolChild .Write
        out.physical.offset (out.physical.offset+1) := by
  have treeEq : (child Q.allocation.extra out.boolOutput.global.protectedTags out.sourceOutput.tag out.boolOutput.global.nextPointerTag
      (UInt64.ofNat offset) len .VisitChildrenOfAccessed).tree=CurrentCallResourceSharedStage.tree out := by
    dsimp only [CurrentCallResourceSharedStage.tree]
    exact congrArg (fun a : Allocation Provenance BorrowTree=>
      (child a.extra out.boolOutput.global.protectedTags out.sourceOutput.tag out.boolOutput.global.nextPointerTag
        (UInt64.ofNat offset) len .VisitChildrenOfAccessed).tree) allocation
  have seed:=CurrentCallResourceSharedBoolFrame.same out ready Q pointer allocation completion sameId stage
  obtain ⟨⟨node,nodeAt,nodeTag,nodeParent,nodeChildren,nodeHidden⟩,activity⟩:=
    CurrentCallResourceSharedBoolFrame.same_facets out ready Q pointer allocation sameId stage
  rw [treeEq] at seed nodeAt activity
  have different : out.boolChild≠stage.reader := by
    intro equal
    have same:=Option.some.inj ((equal ▸ nodeAt).symm.trans P.readerAt)
    exact bool_tag_before_shared out (nodeTag.symm.trans ((congrArg TreeNode.tag same).trans P.readerTag))
  have nonzero : len≠0 := by intro zero;have pos:=C.positive;rw [zero] at pos;contradiction
  obtain ⟨helper,lookup,owned,facets,active⟩:=CurrentCallOptionalLenBoolFrame.construct
    (CurrentCallResourceSharedStage.tree out) (CurrentCallResourceLenInvoke.held out ready).global id
    (S05ConcreteProtectedChildCompletion.extend Q.precise.completion stage.reader Q.pointer.grant)
    P.runtime P.parents P.primarySlot P.distinct P.parents.order stage.preparation.geometry.selectedPosition
    stage.preparation.geometry.selectedRoot Q.pointer.grant stage.reader out.boolChild P.rootNode P.readerNode node
    P.primaryBelow P.rootSlot P.rootAt P.sourcePath P.readerAt P.readerPath P.readerEdge P.readerHidden P.readerUnheld
    nodeAt (nodeChildren.trans (CurrentCallResourceBoolFacets.current out).1)
    (nodeHidden.trans (CurrentCallResourceBoolFacets.current out).2.1) different
    (CurrentCallResourceLenInvoke.helper_room out ready) (UInt64.ofNat offset) len out.physical.offset (out.physical.offset+1)
    nonzero P.bounds (by have margin:=P.margin;omega) P.margin (same_range out sameId) P.readable P.owned seed activity
  rw [P.readerTag] at lookup owned facets active
  have actualTree :
      (((CurrentCallResourceSharedStage.tree out).performBorrowAccessRange
        (.concrete out.boolOutput.global.nextPointerTag) (Size.ofBytes (UInt64.ofNat offset)) (Size.ofBytes len) .Read
        (registered (CurrentCallResourceLenInvoke.held out ready).global {} id
          (CurrentCallResourceLenInvoke.helper_room out ready)).1.protectedTags .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes (UInt64.ofNat offset)) (.concrete out.boolOutput.global.nextPointerTag)
        (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag
        (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true).tree =
      CurrentCallResourceLenInvoke.borrowedTree out ready := by
    rfl
  rw [actualTree] at lookup owned facets active
  have flags : ((registered (CurrentCallResourceLenInvoke.held out ready).global {} id
      (CurrentCallResourceLenInvoke.helper_room out ready)).1.endCall
      (registered (CurrentCallResourceLenInvoke.held out ready).global {} id
        (CurrentCallResourceLenInvoke.helper_room out ready)).2).protectedTags=
      (CurrentCallResourceLenReturn.postTracker out ready).global.protectedTags := by rfl
  rw [flags] at owned
  have releaseFlags : (registered (CurrentCallResourceLenInvoke.held out ready).global {} id
      (CurrentCallResourceLenInvoke.helper_room out ready)).1.protectedTags=
      (CurrentCallResourceLenReturn.liveTracker out ready).global.protectedTags := by rfl
  have releasedEq : ((CurrentCallResourceLenInvoke.borrowedTree out ready).releaseProtector
      (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag
      (registered (CurrentCallResourceLenInvoke.held out ready).global {} id
        (CurrentCallResourceLenInvoke.helper_room out ready)).1.protectedTags).tree=
      CurrentCallResourceLenReturn.releasedTree out ready := by
    dsimp only [CurrentCallResourceLenReturn.releasedTree]
    rw [releaseFlags]
  rw [releasedEq] at owned facets active
  refine ⟨helper,lookup,?_,?_,?_⟩
  · exact owned
  · obtain ⟨next,present,tag,parent,children,hidden⟩:=facets
    exact ⟨next,present,tag.trans nodeTag,parent.trans nodeParent,children.trans nodeChildren,hidden.trans nodeHidden⟩
  · exact active

theorem same {nextData nextOwner}
    (Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut)
    (pointer : Q.pointer=CurrentCallResourceSourceAfterBool.pointer out)
    (allocation : Q.allocation=(CurrentCallResourceSourceFinal.entry out).allocation)
    (completion : Q.precise.completion=CurrentCallResourceSourceFinal.completion out)
    (sameId : out.physical.id=id)
    (stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len
      (CurrentCallResourceBodyReadiness.current_room out ready))
    :
    ∃ helper,
      (CurrentCallResourceLenInvoke.borrowedTree out ready).indexOfTag
        (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag=some helper ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority (CurrentCallResourceLenReturn.releasedTree out ready)
        (S05ConcreteProtectedChildCompletion.extend
          (S05ConcreteProtectedChildCompletion.extend Q.precise.completion stage.reader Q.pointer.grant) helper stage.reader)
        (CurrentCallResourceLenReturn.postTracker out ready).global.protectedTags out.boolChild)
        out.physical.offset (out.physical.offset+1) (CurrentCallResourceLenReturn.releasedTree out ready).locations ∧
      (∃ node,(CurrentCallResourceLenReturn.releasedTree out ready).nodeAt out.boolChild=some node ∧
        node.tag=out.boolNode.tag ∧ node.parent=out.boolNode.parent ∧ node.children=out.boolNode.children ∧ node.isExposed=out.boolNode.isExposed) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin (CurrentCallResourceLenReturn.releasedTree out ready) out.boolChild .Write
        out.physical.offset (out.physical.offset+1) := by
  obtain ⟨P⟩:=CurrentCallResourceLenReturn.preStrongSnapshot out ready Q pointer allocation stage
  exact same_of_preStrong out ready Q pointer allocation completion sameId stage P

theorem same_dropped {nextData nextOwner}
    (Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut)
    (pointer : Q.pointer=CurrentCallResourceSourceAfterBool.pointer out)
    (allocation : Q.allocation=(CurrentCallResourceSourceFinal.entry out).allocation)
    (completion : Q.precise.completion=CurrentCallResourceSourceFinal.completion out)
    (sameId : out.physical.id=id)
    (stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len
      (CurrentCallResourceBodyReadiness.current_room out ready))
    (dropped : CurrentCallResourceLenReturn.Dropped out ready Q stage) :
      OwnedOn (S05CompletedAncestryReadMutable.Authority (CurrentCallResourceLenReturn.releasedTree out ready)
        (S05ConcreteProtectedChildCompletion.extend
          (S05ConcreteProtectedChildCompletion.extend Q.precise.completion stage.reader Q.pointer.grant) dropped.helperIndex stage.reader)
        (CurrentCallResourceLenReturn.postTracker out ready).global.protectedTags out.boolChild)
        out.physical.offset (out.physical.offset+1) (CurrentCallResourceLenReturn.releasedTree out ready).locations ∧
      (∃ node,(CurrentCallResourceLenReturn.releasedTree out ready).nodeAt out.boolChild=some node ∧
        node.tag=out.boolNode.tag ∧ node.parent=out.boolNode.parent ∧ node.children=out.boolNode.children ∧ node.isExposed=out.boolNode.isExposed) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin (CurrentCallResourceLenReturn.releasedTree out ready) out.boolChild .Write
        out.physical.offset (out.physical.offset+1) := by
  obtain ⟨helper,lookup,owned,facets,active⟩:=same out ready Q pointer allocation completion sameId stage
  have equal : helper=dropped.helperIndex:=Option.some.inj (lookup.symm.trans dropped.lookup)
  subst helper
  exact ⟨owned,facets,active⟩

/-- The actual shared-reference source update preserves the disjoint Bool row. -/
theorem different_live_before (differentId : out.physical.id≠id) :
    (CurrentCallResourceSharedStage.afterMachine out ready).memory.live.find? (fun row=>row.1==out.physical.id)=
      some (out.physical.id,{out.physical.entry with allocation:=out.updated}) := by
  have initial : (CurrentCallResourceSharedStage.machine out).memory.live.find? (fun row=>row.1==out.physical.id)=
      some (out.physical.id,{out.physical.entry with allocation:=out.updated}) := by
    rw [CurrentCallResourceSharedStage.memory,out.finalMachineEq]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  exact StackPopRelease.lookup_commit_other (CurrentCallResourceSharedStage.machine out).memory id out.physical.id
    (CurrentCallResourceSourceFinal.entry out) {out.physical.entry with allocation:=out.updated}
    (CurrentCallResourceSharedStage.tree out) differentId initial

/-- A helper operating on the distinct source allocation leaves the Bool tree
literal, while the actual singleton registration/removal preserves its rows. -/
theorem different (differentId : out.physical.id≠id) :
    OwnedOn (S05CompletedAncestryReadMutable.Authority out.updated.extra
      (S05ConcreteProtectedChildCompletion.extend out.R.completion out.boolChild C.V.pointer.grant)
      (CurrentCallResourceLenReturn.postTracker out ready).global.protectedTags out.boolChild)
      out.physical.offset (out.physical.offset+1) out.updated.extra.locations ∧
    out.updated.extra.nodes.get out.boolChild=some out.boolNode ∧ out.boolNode.children=#[] ∧
      out.boolNode.isExposed=false ∧ GeneralBorrowFreshActiveWithin.ActiveWithin out.updated.extra out.boolChild .Write
        out.physical.offset (out.physical.offset+1) := by
  have fresh : ∀ index node,out.updated.extra.nodes.get index=some node →
      node.tag≠(CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag := by
    intro index node present same
    have old:=GeneralBorrowParentTagInvariant.parent_below_fresh out.updated.extra out.boolOutput.global out.afterRuntime index node present
    have next:=GenericFunctionEntryNumerics.successor_value out.boolOutput.global.nextPointerTag
      (CurrentCallResourceBodyReadiness.current_room out ready)
    have equal:=congrArg (fun tag : BorTag=>tag.value.toNat) same
    change node.tag.value.toNat=(TypedRetagEmpty.successorTag out.boolOutput.global.nextPointerTag
      (CurrentCallResourceBodyReadiness.current_room out ready)).value.toNat at equal
    have less:=UInt64.lt_iff_toNat_lt.mp old
    omega
  have retained:=untouched out.updated.extra (CurrentCallResourceLenInvoke.held out ready).global
    (S05ConcreteProtectedChildCompletion.extend out.R.completion out.boolChild C.V.pointer.grant)
    out.boolChild id (CurrentCallResourceLenInvoke.helper_room out ready) fresh out.physical.offset (out.physical.offset+1)
    (CurrentCallResourceSharedBoolFrame.different out differentId)
  obtain ⟨present,_,leaf,hidden,active⟩:=CurrentCallResourceSharedBoolFrame.different_facets out differentId
  exact ⟨retained,present,leaf,hidden,active⟩

def boolAllocation : Allocation Provenance BorrowTree :=
  if out.physical.id=id then (CurrentCallResourceLenInvoke.entry out).allocation.setExtra
    (CurrentCallResourceLenReturn.releasedTree out ready) else out.updated

def boolCompletion {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len
      (CurrentCallResourceBodyReadiness.current_room out ready)}
    (result : CurrentCallResourceLenReturn.Result out ready Q stage) : Completion :=
  if out.physical.id=id then result.completion else
    S05ConcreteProtectedChildCompletion.extend out.R.completion out.boolChild C.V.pointer.grant

/-- Attach the retained Bool child to the SAME actual helper-return machine.
The allocation is obtained from the real live heap after the release and pop. -/
theorem result {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len
      (CurrentCallResourceBodyReadiness.current_room out ready)}
    (returned : CurrentCallResourceLenReturn.Result out ready Q stage) :
    Present (ActualWorld returned.machine) out.physical.id (boolAllocation out ready) ∧
    OwnedOn (S05CompletedAncestryReadMutable.Authority (boolAllocation out ready).extra
      (boolCompletion out ready returned) (CurrentCallResourceLenReturn.postTracker out ready).global.protectedTags out.boolChild)
      out.physical.offset (out.physical.offset+1) (boolAllocation out ready).extra.locations ∧
    (∃ node,(boolAllocation out ready).extra.nodeAt out.boolChild=some node ∧
      node.tag=out.boolNode.tag ∧ node.parent=out.boolNode.parent ∧ node.children=#[] ∧ node.isExposed=false) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin (boolAllocation out ready).extra out.boolChild .Write
      out.physical.offset (out.physical.offset+1) := by
  by_cases sameId : out.physical.id=id
  · obtain ⟨owned,⟨node,nodeAt,tag,parent,children,hidden⟩,activity⟩:=same_dropped out ready Q
      returned.sourcePointer returned.sourceAllocation returned.sourceCompletion sameId stage returned.toDropped
    have actualPresent : Present (ActualWorld returned.machine) id
        ((CurrentCallResourceLenInvoke.entry out).allocation.setExtra (CurrentCallResourceLenReturn.releasedTree out ready)) := by
      simp only [Present,ActualWorld,Array.toList_map]
      exact List.mem_map.mpr ⟨_,Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some returned.sourceLive),rfl⟩
    have actualFacets : ∃ next,(CurrentCallResourceLenReturn.releasedTree out ready).nodeAt out.boolChild=some next ∧
        next.tag=out.boolNode.tag ∧ next.parent=out.boolNode.parent ∧ next.children=#[] ∧ next.isExposed=false :=
      ⟨node,nodeAt,tag,parent,children.trans (CurrentCallResourceBoolFacets.current out).1,
      hidden.trans (CurrentCallResourceBoolFacets.current out).2.1⟩
    have allocationEq : boolAllocation out ready=(CurrentCallResourceLenInvoke.entry out).allocation.setExtra
        (CurrentCallResourceLenReturn.releasedTree out ready) := by
      dsimp only [boolAllocation]
      rw [ite_eq_left sameId]
    have extraEq := congrArg Allocation.extra allocationEq
    dsimp only [Allocation.setExtra,Allocation.mapExtra] at extraEq
    have completionEq : boolCompletion out ready returned=
        S05ConcreteProtectedChildCompletion.extend
          (S05ConcreteProtectedChildCompletion.extend Q.precise.completion stage.reader Q.pointer.grant) returned.helperIndex stage.reader := by
      dsimp only [boolCompletion,CurrentCallResourceLenReturn.Result.completion]
      rw [ite_eq_left sameId]
    refine ⟨?_,?_,?_,?_⟩
    · rw [allocationEq,sameId];exact actualPresent
    · rw [extraEq,completionEq];exact owned
    · rw [extraEq];exact actualFacets
    · rw [extraEq];exact activity
  · obtain ⟨owned,nodeAt,leaf,hidden,activity⟩:=different out ready sameId
    have actualLive : returned.machine.memory.live.find? (fun row=>row.1==out.physical.id)=
        some (out.physical.id,{out.physical.entry with allocation:=out.updated}) := by
      rw [returned.memory]
      exact StackPopRelease.lookup_commit_other (CurrentCallResourceSharedStage.afterMachine out ready).memory id out.physical.id
        (CurrentCallResourceLenInvoke.entry out) {out.physical.entry with allocation:=out.updated}
        (CurrentCallResourceLenReturn.releasedTree out ready) sameId (different_live_before out ready sameId)
    have actualPresent : Present (ActualWorld returned.machine) out.physical.id out.updated := by
      simp only [Present,ActualWorld,Array.toList_map]
      exact List.mem_map.mpr ⟨_,Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some actualLive),rfl⟩
    have actualFacets : ∃ next,out.updated.extra.nodeAt out.boolChild=some next ∧
        next.tag=out.boolNode.tag ∧ next.parent=out.boolNode.parent ∧ next.children=#[] ∧ next.isExposed=false :=
      ⟨out.boolNode,nodeAt,rfl,rfl,leaf,hidden⟩
    have allocationEq : boolAllocation out ready=out.updated := by
      dsimp only [boolAllocation]
      rw [ite_eq_right sameId]
    have extraEq := congrArg Allocation.extra allocationEq
    have completionEq : boolCompletion out ready returned=
        S05ConcreteProtectedChildCompletion.extend out.R.completion out.boolChild C.V.pointer.grant := by
      dsimp only [boolCompletion]
      rw [ite_eq_right sameId]
    refine ⟨?_,?_,?_,?_⟩
    · rw [allocationEq];exact actualPresent
    · rw [extraEq,completionEq];exact owned
    · rw [extraEq];exact actualFacets
    · rw [extraEq];exact activity

end
end DuplicatePrefix.CurrentCallResourceLenBoolFrame
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceLenBoolFrame" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual Len Bool frame dependency {dependency}"
