import duplicate_prefix.CurrentCallLenRootData
import duplicate_prefix.CurrentCallAsMutBoolFrame
import duplicate_prefix.GeneralBorrowSharedFnEntryGlobalReturn
import duplicate_prefix.StackPopRelease

namespace DuplicatePrefix.CurrentCallAsMutBoolData
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

def literal (tree : BorrowTree) (global : GlobalState) (allocation : AllocId)
    (room : global.nextPointerTag.value < 18446744073709551615) (tag : BorTag) (offset len : UInt64) : GeneralBorrowForestFnEntry.Output :=
  let registration := GeneralBorrowFnEntryRegistration.registered global {} allocation room
  let accessed := tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registration.1.protectedTags .VisitChildrenOfAccessed
  ⟨registration.1,registration.2,global.nextPointerTag,accessed,
    accessed.tree.newChild (Size.ofBytes offset) (.concrete tag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true⟩

private theorem literal_operation (tree : BorrowTree) (global : GlobalState) (allocation : AllocId)
    (room : global.nextPointerTag.value < 18446744073709551615) (tag : BorTag) (offset len : UInt64) :
    GeneralBorrowForestFnEntry.operation tree global {} allocation tag offset len .VisitChildrenOfAccessed =
      .ok (literal tree global allocation room tag offset len) := by
  simp only [GeneralBorrowForestFnEntry.operation,TypedRetagEmpty.allocate_tag global room,Except.bind,Except.pure,bind,pure]
  rfl

/-- The actual AsMut operation, helper release and returned heap retain the
same Bool resource record. Source operation witnesses are derived by the
existing call theorem; the Bool authority is derived here. -/
theorem of_return {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (held : MachineHooks.BorrowState) (completion : Completion)
    (boolData : CurrentCallLenRootData.Data s machine entry held completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra held.global)
    (complete : Completes entry.allocation.extra completion) (order : ParentTagOrder entry.allocation.extra)
    (position : Nat) (selected parent : UniIndex) (selectedNode parentNode : TreeNode)
    (slot : entry.allocation.extra.roots[position]? = some selected)
    (selectedAt : entry.allocation.extra.nodes.get selected = some selectedNode)
    (parentAt : entry.allocation.extra.nodeAt parent = some parentNode) (path : Path entry.allocation.extra selected parent)
    (different : call.sourceId = call.returnId → s.out.borrowed.child ≠ parent)
    (room : held.global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : entry.allocation.extra.nodes.size+1 ≤ 4294967295)
    (short : entry.allocation.extra.nodes.size+1 < 65536) (nonzero : len ≠ 0)
    (bounds : (UInt64.ofNat call.sourceOffset).toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority entry.allocation.extra completion held.global.protectedTags parent)
      (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) entry.allocation.extra.locations)
    (disjoint : call.sourceId = call.returnId →
      (UInt64.ofNat call.sourceOffset+len).toNat ≤ (UInt64.ofNat call.returnOffset).toNat ∨
      (UInt64.ofNat call.returnOffset+1).toNat ≤ (UInt64.ofNat call.sourceOffset).toNat)
    (output : GeneralBorrowForestFnEntry.Output) (helper : UniIndex)
    (actual : GeneralBorrowForestFnEntry.operation entry.allocation.extra held.global {} call.sourceId parentNode.tag
      (UInt64.ofNat call.sourceOffset) len .VisitChildrenOfAccessed = .ok output)
    (lookup : output.child.tree.indexOfTag output.tag = some helper)
    (helperNode : ∃ node, output.child.tree.nodeAt helper = some node ∧ node.tag = output.tag)
    (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (afterEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (afterHeld : MachineHooks.BorrowState)
    (postMemory : post.memory = RetagEntry.updatedMemory machine.memory call.sourceId entry
      (output.child.tree.releaseProtector output.tag output.global.protectedTags).tree)
    (afterLive : post.memory.live.find? (fun row => row.1 == call.sourceId) = some (call.sourceId,afterEntry))
    (afterGlobal : afterHeld.global = output.global.endCall output.frame)
    (afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts afterEntry.allocation.extra afterHeld.global)
    (afterComplete : Completes afterEntry.allocation.extra (extend completion helper parent))
    (afterOrder : ParentTagOrder afterEntry.allocation.extra)
    (afterOld : ∀ index node, entry.allocation.extra.nodes.get index = some node →
      ∃ next, afterEntry.allocation.extra.nodes.get index = some next ∧ next.tag = node.tag ∧
        next.parent = node.parent ∧ next.isExposed = node.isExposed) :
    Nonempty (CurrentCallLenRootData.Data s post afterEntry afterHeld (extend completion helper parent)) ∧
      s.out.borrowed.output.tag ≠ output.tag := by
  let resultTree := (output.child.tree.releaseProtector output.tag output.global.protectedTags).tree
  have entryEq : afterEntry = {entry with allocation := entry.allocation.setExtra resultTree} := by
    have current : post.memory.live.find? (fun row => row.1 == call.sourceId) =
        some (call.sourceId,{entry with allocation := entry.allocation.setExtra resultTree}) := by
      rw [postMemory]
      exact MemoryCopyBridge.live_lookup_replaced machine.memory call.sourceId _
    exact (Prod.mk.inj (Option.some.inj (afterLive.symm.trans current))).2
  have treeEq : afterEntry.allocation.extra = resultTree := by rw [entryEq];rfl
  have outputEq : output = literal entry.allocation.extra held.global call.sourceId room parentNode.tag (UInt64.ofNat call.sourceOffset) len :=
    Except.ok.inj (actual.symm.trans (literal_operation entry.allocation.extra held.global call.sourceId room parentNode.tag (UInt64.ofNat call.sourceOffset) len))
  have globalEq : afterHeld.global = GeneralBorrowFnEntryRegistration.advanced held.global room := by
    rw [afterGlobal,outputEq]
    exact GeneralBorrowSharedFnEntryGlobalReturn.global entry.allocation.extra held.global runtime {} call.sourceId room
  have flagsEq : afterHeld.global.protectedTags = held.global.protectedTags := by rw [globalEq];rfl
  have raised : held.global.nextPointerTag.value.toNat ≤ afterHeld.global.nextPointerTag.value.toNat := by
    rw [globalEq]
    have increment := GenericFunctionEntryNumerics.successor_value held.global.nextPointerTag room
    change held.global.nextPointerTag.value.toNat ≤ (TypedRetagEmpty.successorTag held.global.nextPointerTag room).value.toNat
    omega
  have boolTagNe : boolData.node.tag ≠ output.tag := by
    rw [outputEq]
    apply GeneralBorrowForestTagHighWater.different
    exact GeneralBorrowForestTagHighWater.mapped boolData.entry.allocation.extra _ _ _ boolData.runtime.below s.out.borrowed.child
      (boolData.runtime.formed.allocator.nodeTags s.out.borrowed.child boolData.node boolData.present)
  refine ⟨?_,fun equal => boolTagNe (boolData.tag.trans equal)⟩
  by_cases same : call.sourceId = call.returnId
  · have beforeEntryEq := boolData.sameEntry same
    have completionEq := boolData.sameCompletion same
    have bAt : entry.allocation.extra.nodeAt s.out.borrowed.child = some boolData.node := by simpa only [beforeEntryEq] using boolData.present
    have bOwned : OwnedOn (Authority entry.allocation.extra completion held.global.protectedTags s.out.borrowed.child)
        (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) entry.allocation.extra.locations := by
      simpa only [beforeEntryEq,completionEq] using boolData.owned
    have bActive : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra s.out.borrowed.child .Write
        (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) := by simpa only [beforeEntryEq] using boolData.active
    have bBounds : (UInt64.ofNat call.returnOffset).toNat+1 ≤ entry.allocation.extra.locations.size.bytes.toNat := by
      simpa only [beforeEntryEq] using boolData.bounds
    obtain ⟨framed,framedHelper,framedActual,framedTag,framedLookup,released,frame,_,_,capacity,growth,retained,
      ⟨node,nodeAt,nodeTag,nodeParent,nodeLeaf,nodeHidden⟩,active⟩ := CurrentCallAsMutBoolFrame.invoke entry.allocation.extra held.global call.sourceId completion
      runtime complete order position selected parent s.out.borrowed.child selectedNode parentNode boolData.node slot selectedAt parentAt path
      bAt boolData.leaf boolData.hidden (different same) room nodeRoom short (UInt64.ofNat call.sourceOffset) len (UInt64.ofNat call.returnOffset)
      nonzero bounds bBounds (disjoint same) owned bOwned bActive
    have sameOutput : framed = output := Except.ok.inj (framedActual.symm.trans actual)
    subst framed
    have sameHelper : framedHelper = helper := Option.some.inj (framedLookup.symm.trans lookup)
    subst framedHelper
    change resultTree = {output.child.tree with locations := resultTree.locations} at frame
    change resultTree.nodes.size ≤ entry.allocation.extra.nodes.size+1 at growth
    obtain ⟨freshNode,freshAt,freshTag⟩ := helperNode
    have helperDifferent : s.out.borrowed.child ≠ helper := by
      intro equal
      have found : resultTree.nodeAt helper = some node := by simpa only [equal] using nodeAt
      have freshReleased : resultTree.nodeAt helper = some freshNode := by rw [frame];exact freshAt
      have nodeEq := Option.some.inj (found.symm.trans freshReleased)
      exact boolTagNe (nodeTag.symm.trans ((congrArg TreeNode.tag nodeEq).trans freshTag))
    have edge : (extend completion helper parent).parents[s.out.borrowed.child.toNat]? = some (some s.out.source.base.raw.returnPointer.grant) := by
      have bounded : s.out.borrowed.child.toNat < completion.parents.size := by
        rw [complete.1]
        exact GeneralBorrowNodeUpdate.lookup_valid _ _ _ bAt
      rw [old_parent _ helper parent s.out.borrowed.child helperDifferent bounded]
      simpa only [completionEq] using boolData.edge
    obtain ⟨original,originalAt,originalTag,_,originalHidden⟩ := afterOld s.out.source.base.raw.returnPointer.grant boolData.originalNode
      (by simpa only [beforeEntryEq,BorrowTree.nodeAt] using boolData.originalPresent)
    have provenance := boolData.originalProvenance
    have originalProvenance : match s.out.source.base.raw.returnPointer.value.provenance with
      | .concrete _ tag => tag = original.tag | .wildcard => original.isExposed = true := by
      cases prov : s.out.source.base.raw.returnPointer.value.provenance with
      | concrete id tag =>
        have before : tag = boolData.originalNode.tag := by simpa only [prov] using provenance
        exact before.trans originalTag.symm
      | wildcard => exact originalHidden.trans (by simpa only [prov] using provenance)
    have boolBounds : (UInt64.ofNat call.returnOffset).toNat+1 ≤ afterEntry.allocation.extra.locations.size.bytes.toNat := by
      rw [treeEq,capacity]
      exact bBounds
    have boolOwned : OwnedOn (Authority afterEntry.allocation.extra (extend completion helper parent) afterHeld.global.protectedTags s.out.borrowed.child)
        (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) afterEntry.allocation.extra.locations := by
      rw [treeEq,afterGlobal]
      exact retained
    have boolAt : afterEntry.allocation.extra.nodeAt s.out.borrowed.child = some node := by rw [treeEq];exact nodeAt
    have boolActive : GeneralBorrowFreshActiveWithin.ActiveWithin afterEntry.allocation.extra s.out.borrowed.child .Write
        (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) := by rw [treeEq];exact active
    have boolShort : afterEntry.allocation.extra.nodes.size < 65536 := by rw [treeEq];omega
    exact ⟨⟨afterEntry,extend completion helper parent,by simpa only [same] using afterLive,(fun _=>rfl),(fun _=>rfl),afterRuntime,afterComplete,
      afterOrder,boolShort,node,boolAt,nodeTag.trans boolData.tag,nodeLeaf.trans boolData.leaf,nodeHidden.trans boolData.hidden,boolActive,boolOwned,edge,
      original,originalAt,originalProvenance,boolBounds,fun separate=>False.elim (separate same)⟩⟩
  · have boolLive : post.memory.live.find? (fun row => row.1 == call.returnId) = some (call.returnId,boolData.entry) := by
      rw [postMemory]
      exact StackPopRelease.lookup_commit_other machine.memory call.sourceId call.returnId entry boolData.entry resultTree (Ne.symm same) boolData.live
    have boolRuntime : DuplicatePrefixBorrowContract.RuntimeFacts boolData.entry.allocation.extra afterHeld.global := by
      refine ⟨?_,?_,boolData.runtime.possible,?_⟩
      · rw [flagsEq];exact boolData.runtime.formed
      · rw [flagsEq];exact boolData.runtime.coherent
      · rw [flagsEq]
        exact GeneralBorrowForestTagHighWaterHistory.weaken _ _ _ _ boolData.runtime.below raised
    have boolOwned : OwnedOn (Authority boolData.entry.allocation.extra boolData.completion afterHeld.global.protectedTags s.out.borrowed.child)
        (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) boolData.entry.allocation.extra.locations := by
      rw [flagsEq];exact boolData.owned
    exact ⟨⟨boolData.entry,boolData.completion,boolLive,(fun equal=>False.elim (same equal)),(fun equal=>False.elim (same equal)),boolRuntime,
      boolData.completes,boolData.order,boolData.short,boolData.node,boolData.present,boolData.tag,boolData.leaf,boolData.hidden,boolData.active,boolOwned,boolData.edge,
      boolData.originalNode,boolData.originalPresent,boolData.originalProvenance,boolData.bounds,boolData.sourceAbsent⟩⟩

end
end DuplicatePrefix.CurrentCallAsMutBoolData
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallAsMutBoolData").length > 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved AsMut Bool data dependency {dependency}"
