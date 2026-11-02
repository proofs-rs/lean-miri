import duplicate_prefix.CurrentCallLenRootData
import duplicate_prefix.CurrentCallDefaultMutableBoolFrame
import duplicate_prefix.StackPopRelease

namespace DuplicatePrefix.CurrentCallDefaultMutableBoolData
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership GeneralBorrowProjection GeneralRangeMapOrigins
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder
open S05ConcreteProtectedChildCompletion CurrentCallLen
open S05CompletedAncestryReadMutable (Authority)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def borrowedTree (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (held : MachineHooks.BorrowState) (tag : BorTag) (offset len : UInt64) : BorrowTree :=
  (GeneralBorrowRawDefaultExpression.child entry.allocation.extra held.global.protectedTags tag held.global.nextPointerTag
    offset len .VisitChildrenOfAccessed).tree

/-- Transport the derived Bool data through the literal Default mutable Ref
heap and tag update. The source statement's output supplies its actual new
completion and old-node metadata; Bool rights come from the disjoint frame. -/
theorem of_statement {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (held : MachineHooks.BorrowState) (completion : Completion)
    (boolData : CurrentCallLenRootData.Data s machine entry held completion)
    (_live : machine.memory.live.find? (fun row => row.1 == call.sourceId) = some (call.sourceId,entry))
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra held.global)
    (complete : Completes entry.allocation.extra completion) (order : ParentTagOrder entry.allocation.extra)
    (parentNode : TreeNode) (parentAt : entry.allocation.extra.nodeAt s.out.source.base.raw.child = some parentNode)
    (parentTag : parentNode.tag = s.out.source.base.raw.output.tag)
    (room : held.global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : entry.allocation.extra.nodes.size+1 ≤ 4294967295)
    (short : entry.allocation.extra.nodes.size+1 < 65536) (nonzero : len ≠ 0)
    (bounds : (UInt64.ofNat call.sourceOffset).toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority entry.allocation.extra completion held.global.protectedTags s.out.source.base.raw.child)
      (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) entry.allocation.extra.locations)
    (disjoint : call.sourceId = call.returnId → ∀ point : UInt64,
      (UInt64.ofNat call.returnOffset).toNat ≤ point.toNat → point.toNat < (UInt64.ofNat call.returnOffset+1).toNat →
      point.toNat < (UInt64.ofNat call.sourceOffset).toNat ∨ (UInt64.ofNat call.sourceOffset+len).toNat ≤ point.toNat)
    (child : UniIndex)
    (lookup : (borrowedTree entry held parentNode.tag (UInt64.ofNat call.sourceOffset) len).indexOfTag held.global.nextPointerTag = some child)
    (afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts (borrowedTree entry held parentNode.tag (UInt64.ofNat call.sourceOffset) len)
      (ReferenceBorrowDriver.allocatedTracker held room).global)
    (afterComplete : Completes (borrowedTree entry held parentNode.tag (UInt64.ofNat call.sourceOffset) len) (extend completion child s.out.source.base.raw.child))
    (afterOrder : ParentTagOrder (borrowedTree entry held parentNode.tag (UInt64.ofNat call.sourceOffset) len))
    (afterNode : ∃ node, (borrowedTree entry held parentNode.tag (UInt64.ofNat call.sourceOffset) len).nodeAt child = some node ∧ node.tag = held.global.nextPointerTag)
    (afterOld : ∀ index node, entry.allocation.extra.nodes.get index = some node →
      ∃ next, (borrowedTree entry held parentNode.tag (UInt64.ofNat call.sourceOffset) len).nodes.get index = some next ∧
        next.tag = node.tag ∧ next.parent = node.parent ∧ next.isExposed = node.isExposed) :
    let resultTree := borrowedTree entry held parentNode.tag (UInt64.ofNat call.sourceOffset) len
    let resultEntry := {entry with allocation := entry.allocation.setExtra resultTree}
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine held room with
      memory := RetagEntry.updatedMemory machine.memory call.sourceId entry resultTree}
    Nonempty (CurrentCallLenRootData.Data s resultMachine resultEntry (ReferenceBorrowDriver.allocatedTracker held room)
      (extend completion child s.out.source.base.raw.child)) := by
  let resultTree := borrowedTree entry held parentNode.tag (UInt64.ofNat call.sourceOffset) len
  let resultEntry := {entry with allocation := entry.allocation.setExtra resultTree}
  let resultHeld := ReferenceBorrowDriver.allocatedTracker held room
  let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine held room with
    memory := RetagEntry.updatedMemory machine.memory call.sourceId entry resultTree}
  have flags : resultHeld.global.protectedTags = held.global.protectedTags := rfl
  have currentStep : resultHeld.global.nextPointerTag.value.toNat = held.global.nextPointerTag.value.toNat+1 :=
    GenericFunctionEntryNumerics.successor_value held.global.nextPointerTag room
  have boolTagNe : boolData.node.tag ≠ held.global.nextPointerTag := by
    apply GeneralBorrowForestTagHighWater.different
    exact GeneralBorrowForestTagHighWater.mapped boolData.entry.allocation.extra _ _ _ boolData.runtime.below s.out.borrowed.child
      (boolData.runtime.formed.allocator.nodeTags s.out.borrowed.child boolData.node boolData.present)
  by_cases same : call.sourceId = call.returnId
  · have entryEq := boolData.sameEntry same
    have completionEq := boolData.sameCompletion same
    have bAt : entry.allocation.extra.nodeAt s.out.borrowed.child = some boolData.node := by simpa only [entryEq] using boolData.present
    have bOwned : OwnedOn (Authority entry.allocation.extra completion held.global.protectedTags s.out.borrowed.child)
        (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) entry.allocation.extra.locations := by
      simpa only [entryEq,completionEq] using boolData.owned
    have bActive : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra s.out.borrowed.child .Write
        (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) := by simpa only [entryEq] using boolData.active
    have different : s.out.borrowed.child ≠ s.out.source.base.raw.child := by
      intro equal
      have found : entry.allocation.extra.nodes.get s.out.source.base.raw.child = some boolData.node := by
        simpa only [equal,BorrowTree.nodeAt] using bAt
      have nodeEq := Option.some.inj (found.symm.trans parentAt)
      have tags := CurrentCallEntryProtectionData.source_bool_tags_ne s.out.source.base.raw s.out.borrowed
      exact tags (parentTag.symm.trans ((congrArg TreeNode.tag nodeEq).symm.trans boolData.tag))
    obtain ⟨position,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path entry.allocation.extra runtime.formed.toGraphState
      s.out.source.base.raw.child parentNode parentAt
    obtain ⟨_,_,_,capacity,growth,freshChild,freshLookup,preserved,⟨node,nodeAt,nodeTag,nodeParent,nodeLeaf,nodeHidden⟩,active⟩ :=
      CurrentCallDefaultMutableBoolFrame.construct entry.allocation.extra held.global completion runtime complete order
        position root s.out.source.base.raw.child s.out.borrowed.child rootNode parentNode boolData.node slot rootAt parentAt path
        bAt boolData.leaf boolData.hidden different room nodeRoom (by omega) (UInt64.ofNat call.sourceOffset) len
        (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) nonzero bounds (disjoint same) owned bOwned bActive
    change resultTree.nodeAt s.out.borrowed.child = some node at nodeAt
    change resultTree.locations.size = entry.allocation.extra.locations.size at capacity
    change resultTree.nodes.size ≤ entry.allocation.extra.nodes.size+1 at growth
    change GeneralBorrowFreshActiveWithin.ActiveWithin resultTree s.out.borrowed.child .Write
      (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) at active
    have sameChild : freshChild = child := Option.some.inj (freshLookup.symm.trans lookup)
    subst freshChild
    obtain ⟨childNode,childAt,childTag⟩ := afterNode
    have childDifferent : s.out.borrowed.child ≠ child := by
      intro equal
      have found : resultTree.nodeAt child = some node := by simpa only [equal] using nodeAt
      have nodeEq := Option.some.inj (found.symm.trans childAt)
      exact boolTagNe (nodeTag.symm.trans ((congrArg TreeNode.tag nodeEq).trans childTag))
    have edge : (extend completion child s.out.source.base.raw.child).parents[s.out.borrowed.child.toNat]? =
        some (some s.out.source.base.raw.returnPointer.grant) := by
      have bounded : s.out.borrowed.child.toNat < completion.parents.size := by
        rw [complete.1]
        exact GeneralBorrowNodeUpdate.lookup_valid _ _ _ bAt
      rw [old_parent _ child s.out.source.base.raw.child s.out.borrowed.child childDifferent bounded]
      simpa only [completionEq] using boolData.edge
    obtain ⟨original,originalAt,originalTag,_,originalHidden⟩ := afterOld s.out.source.base.raw.returnPointer.grant boolData.originalNode (by
      simpa only [entryEq,BorrowTree.nodeAt] using boolData.originalPresent)
    have provenance := boolData.originalProvenance
    have originalProvenance : match s.out.source.base.raw.returnPointer.value.provenance with
      | .concrete _ tag => tag = original.tag | .wildcard => original.isExposed = true := by
      cases prov : s.out.source.base.raw.returnPointer.value.provenance with
      | concrete id tag =>
        have before : tag = boolData.originalNode.tag := by simpa only [prov] using provenance
        exact before.trans originalTag.symm
      | wildcard => exact originalHidden.trans (by simpa only [prov] using provenance)
    have boolBounds : (UInt64.ofNat call.returnOffset).toNat+1 ≤ resultTree.locations.size.bytes.toNat := by
      rw [capacity]
      simpa only [entryEq] using boolData.bounds
    have boolLive : resultMachine.memory.live.find? (fun row => row.1 == call.returnId) = some (call.returnId,resultEntry) := by
      rw [←same]
      exact MemoryCopyBridge.live_lookup_replaced machine.memory call.sourceId resultEntry
    exact ⟨⟨resultEntry,extend completion child s.out.source.base.raw.child,boolLive,(fun _=>rfl),(fun _=>rfl),afterRuntime,afterComplete,
      afterOrder,(by change resultTree.nodes.size < 65536;omega),node,nodeAt,nodeTag.trans boolData.tag,nodeLeaf.trans boolData.leaf,nodeHidden.trans boolData.hidden,
      active,preserved,edge,original,originalAt,originalProvenance,boolBounds,fun separate=>False.elim (separate same)⟩⟩
  · have boolRuntime : DuplicatePrefixBorrowContract.RuntimeFacts boolData.entry.allocation.extra resultHeld.global := by
      refine ⟨boolData.runtime.formed,boolData.runtime.coherent,boolData.runtime.possible,?_⟩
      exact GeneralBorrowForestTagHighWaterHistory.weaken _ _ _ _ boolData.runtime.below (by omega)
    have boolLive : resultMachine.memory.live.find? (fun row => row.1 == call.returnId) = some (call.returnId,boolData.entry) := by
      exact StackPopRelease.lookup_commit_other machine.memory call.sourceId call.returnId entry boolData.entry resultTree (Ne.symm same) boolData.live
    exact ⟨⟨boolData.entry,boolData.completion,boolLive,(fun equal=>False.elim (same equal)),(fun equal=>False.elim (same equal)),
      boolRuntime,boolData.completes,boolData.order,boolData.short,boolData.node,boolData.present,boolData.tag,boolData.leaf,boolData.hidden,
      boolData.active,boolData.owned,boolData.edge,boolData.originalNode,boolData.originalPresent,boolData.originalProvenance,boolData.bounds,boolData.sourceAbsent⟩⟩

end
end DuplicatePrefix.CurrentCallDefaultMutableBoolData
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallDefaultMutableBoolData").length > 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved Default mutable Bool data dependency {dependency}"
