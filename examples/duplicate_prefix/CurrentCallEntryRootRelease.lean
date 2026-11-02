import duplicate_prefix.CurrentCallRootRelease
import duplicate_prefix.CurrentCallRootPhysicalWindow
import duplicate_prefix.CurrentCallEntryProtectionData
import duplicate_prefix.ActualPopPlan
namespace DuplicatePrefix.CurrentCallEntryRootRelease
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall GeneralRangeMapOrigins CanonicalConfigFacts
open S05CompletedAncestryReadMutable (Authority)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Derived release output; public callers supply only original admission and
readiness, never this package or successful operation certificates. -/
structure Released (before : DuplicatePrefixCallSpecification.Before) (tracker : MachineHooks.BorrowState)
    (frame : FrameState) (place : MPlaceTy Provenance) (original : UniIndex)
    (id : AllocId) (offset : UInt64) (pointer : Pointer Provenance) where
  memory : MemoryState Provenance BorrowTree MiriMemoryKind
  plan : StackPopRelease.Plan tracker.global.protectedTags frame.protectedTags.toList before.memory memory
  window : CurrentCallBoolScalarWrite.Window (ActualPopPlan.released before memory tracker frame) place
  binding : CandidateCallBindings.WindowBinding (ActualPopPlan.released before memory tracker frame)
    window.pointer window.id window.offset.toNat 1
  roleId : window.id = id
  roleOffset : window.offset = offset
  rolePointer : window.pointer = pointer
  completion : Completion
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts window.entry.allocation.extra (tracker.global.endCall frame)
  completes : Completes window.entry.allocation.extra completion
  order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder window.entry.allocation.extra
  short : window.entry.allocation.extra.nodes.size < 65536
  node : TreeNode
  present : window.entry.allocation.extra.nodeAt original = some node
  provenance : match window.pointer.provenance with | .concrete _ tag => tag = node.tag | .wildcard => node.isExposed = true
  bounds : window.offset.toNat+1 ≤ window.entry.allocation.extra.locations.size.bytes.toNat
  owned : OwnedOn (Authority window.entry.allocation.extra completion (tracker.global.endCall frame).protectedTags original)
    window.offset (window.offset+1) window.entry.allocation.extra.locations

namespace Entry
variable {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    (out : CurrentCallEntry.Output input #[])

def borrowFrame : FrameState := out.source.base.raw.output.frame.addProtector call.returnId out.borrowed.output.tag

theorem frame_tags :
    (borrowFrame out).protectedTags = #[(call.sourceId,out.source.base.raw.output.tag),(call.returnId,out.borrowed.output.tag)] := by
  have sourceFrame : ({} : FrameState).addProtector call.sourceId tracker.global.nextPointerTag = out.source.base.raw.output.frame :=
    Option.some.inj out.source.base.outputFrame
  rw [borrowFrame,←sourceFrame,out.source.base.raw.tag]
  rfl

theorem frame_tracked (count : UInt64) (facts : CurrentCallEntry.Facts out count) :
    (out.frame count).extra.borrowTracker = some (borrowFrame out) := by
  change some (out.source.base.raw.output.frame.addProtector out.physical.id out.source.base.raw.output.global.nextPointerTag) = _
  rw [facts.returnId,←out.borrowed.tag]
  rfl
theorem frame_control (count : UInt64) (facts : CurrentCallEntry.Facts out count) :
    (out.frame count).extra.dataRace = none ∧ (out.frame count).returnContinuation = .stop true ∧ (out.frame count).vaList = #[] := by
  let initial := CurrentCallEntry.root before #[] place input.machine.settings.noDataRace
  let value := (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
    (CurrentCallTypedFnEntry.changedPointer out.source.base.raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag)
    len ActualReferenceMetadata.reference).imm
  have metadata := PositiveRootInstalledFrame.metadata initial value count {} call.sourceId tracker.global.nextPointerTag
    out.physical.id out.source.base.raw.output.global.nextPointerTag
  have frameEq := facts.frame_installed
  change out.frame count = PositiveRootInstalledFrame.installed initial value count {} call.sourceId tracker.global.nextPointerTag
    out.physical.id out.source.base.raw.output.global.nextPointerTag at frameEq
  rw [←frameEq] at metadata
  exact ⟨metadata.2.2.2.2.2.2.1.trans initial.noClocks,metadata.2.2.2.1,metadata.2.2.2.2.2.1⟩

end Entry
/-- Original entry output derives its actual complete root release Plan and
restores the original Bool grant, for equal or distinct allocation IDs. -/
theorem of_entry {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    (out : CurrentCallEntry.Output input #[]) (count : UInt64) (facts : CurrentCallEntry.Facts out count) (positive : 0 < len.toNat) :
    Nonempty (Released (out.machine count) ⟨out.borrowed.output.global,tracker.retagMode⟩ (Entry.borrowFrame out)
      place out.source.base.raw.returnPointer.grant call.returnId (UInt64.ofNat call.returnOffset) out.source.base.raw.returnPointer.value) := by
  let raw := out.source.base.raw
  let global := out.borrowed.output.global
  let frame := Entry.borrowFrame out
  let completion := S05ConcreteProtectedChildCompletion.extend (CurrentCallBoolProtection.returnCompletion raw) out.borrowed.child raw.returnPointer.grant
  let bEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {out.physical.entry with allocation := out.updated}
  have bLive : (out.machine count).memory.live.find? (fun row => row.1 == call.returnId) = some (call.returnId,bEntry) := by
    simpa only [facts.returnId] using CurrentCallRootPhysicalWindow.bool_live out count
  have bRes := CurrentCallEntryProtectionData.Facts.bool_resources facts
  obtain ⟨qNode,qAt,qTag,qLeaf,qHidden,qActive⟩ := CurrentCallEntryProtectionData.Facts.source_data facts positive
  obtain ⟨bNode,bAt,bTag,bLeaf,bHidden,bActive⟩ := CurrentCallEntryProtectionData.Facts.bool_data facts positive
  have qOwned := CurrentCallEntryProtectionData.Facts.source_authority facts
  have bOwned := CurrentCallEntryProtectionData.Facts.bool_authority facts positive
  have qRes := CurrentCallEntryProtectionData.Facts.source_resources facts
  have frameTags : frame.protectedTags = #[(call.sourceId,qNode.tag),(call.returnId,bNode.tag)] := by
    simpa only [qTag,bTag] using Entry.frame_tags out
  have endpoints := CurrentCallBoolProtection.endpoints (CurrentCallPush.prepared_input input #[]) {} raw positive
  have qPositive : (UInt64.ofNat call.sourceOffset).toNat < (UInt64.ofNat call.sourceOffset+len).toNat := by
    rw [endpoints.1,endpoints.2.2.1];omega
  have bPositive : (UInt64.ofNat call.returnOffset).toNat < (UInt64.ofNat call.returnOffset+1).toNat := by
    rw [endpoints.2.1,endpoints.2.2.2.1];omega
  have output : ∃ memory finalTree,
      StackPopRelease.Plan global.protectedTags frame.protectedTags.toList (out.machine count).memory memory ∧
      memory.live.find? (fun row => row.1 == call.returnId) = some (call.returnId,{bEntry with allocation := bEntry.allocation.setExtra finalTree}) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts finalTree (global.endCall frame) ∧ Completes finalTree completion ∧
      finalTree = {out.updated.extra with locations := finalTree.locations} ∧ finalTree.locations.size = out.updated.extra.locations.size ∧
      OwnedOn (Authority finalTree completion (global.endCall frame).protectedTags raw.returnPointer.grant)
        (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) finalTree.locations := by
    by_cases same : call.sourceId = call.returnId
    · simp only [same,ite_true] at qAt qActive qOwned qRes
      have different : out.borrowed.child ≠ raw.child := by
        intro equal
        have atSame : out.updated.extra.nodes.get raw.child = some bNode := by simpa only [equal] using bAt
        have nodeEq : bNode = qNode := Option.some.inj (atSame.symm.trans qAt)
        have tags := CurrentCallEntryProtectionData.source_bool_tags_ne raw out.borrowed
        exact tags (qTag.symm.trans (nodeEq ▸ bTag))
      have disjoint : (UInt64.ofNat call.sourceOffset+len).toNat ≤ (UInt64.ofNat call.returnOffset).toNat ∨
          (UInt64.ofNat call.returnOffset+1).toNat ≤ (UInt64.ofNat call.sourceOffset).toNat := by
        by_cases left : (UInt64.ofNat call.sourceOffset+len).toNat ≤ (UInt64.ofNat call.returnOffset).toNat
        · exact .inl left
        by_cases after : (UInt64.ofNat call.sourceOffset).toNat ≤ (UInt64.ofNat call.returnOffset).toNat
        · have impossible := endpoints.2.2.2.2.2 same (UInt64.ofNat call.returnOffset) after (by omega)
          omega
        · have earlier := endpoints.2.2.2.2.2 same (UInt64.ofNat call.sourceOffset) (Nat.le_refl _) qPositive
          exact .inr (by omega)
      let first := out.updated.extra.releaseProtector qNode.tag global.protectedTags
      let second := first.tree.releaseProtector bNode.tag global.protectedTags
      let middleEntry := {bEntry with allocation := bEntry.allocation.setExtra first.tree}
      obtain ⟨plan,runtime,complete,shape,capacity,rights⟩ := CurrentCallRootRelease.same_tree_plan out.updated.extra global completion
        bRes.1 bRes.2.1 bRes.2.2.1 call.returnId frame raw.child out.borrowed.child raw.returnPointer.grant qNode bNode
        qAt bAt qHidden bHidden bLeaf different (by simpa only [same] using frameTags) bRes.2.2.2.2
        (UInt64.ofNat call.sourceOffset) len (UInt64.ofNat call.returnOffset) qPositive bPositive disjoint qActive bActive qOwned bOwned bRes.2.2.2.1
        (out.machine count).memory bEntry bLive rfl
      let middle := StackPopRelease.commitTree (out.machine count).memory call.returnId bEntry first.tree
      let memory := StackPopRelease.commitTree middle call.returnId middleEntry second.tree
      refine ⟨memory,second.tree,plan,?_,runtime,complete,shape,capacity,rights⟩
      simpa only [memory,middleEntry,Allocation.setExtra,Allocation.mapExtra] using StackPopRelease.lookup_commit_same middle call.returnId middleEntry second.tree
    · simp only [same,ite_false] at qAt qActive qOwned qRes
      obtain ⟨qEntry,qLive,qExtra,_,_,_,_,_,_,_⟩ := facts.source_allocation positive
      simp only [same,ite_false] at qExtra
      have boolHidden : S04ReturnReleaseParent.HiddenFrame out.updated.extra frame := by
        intro row member index node present tagged
        rw [frameTags] at member
        change row ∈ [(call.sourceId,qNode.tag),(call.returnId,bNode.tag)] at member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with source | dest
        · subst row
          have mapping := bRes.1.formed.allocator.nodeTags index node present
          have absent := CurrentCallEntryProtectionData.Facts.source_tag_absent facts positive same
          rw [tagged,qTag] at mapping
          rw [show out.updated.extra.indexOfTag raw.output.tag = some index from mapping] at absent
          cases absent
        · subst row
          have mapping := bRes.1.formed.allocator.nodeTags index node present
          have actual := bRes.1.formed.allocator.nodeTags out.borrowed.child bNode bAt
          rw [tagged,actual] at mapping
          have equal := Option.some.inj mapping
          subst index
          have nodeEq := Option.some.inj (present.symm.trans bAt)
          subst node;exact bHidden
      let first := raw.output.child.tree.releaseProtector qNode.tag global.protectedTags
      let second := out.updated.extra.releaseProtector bNode.tag global.protectedTags
      let middle := StackPopRelease.commitTree (out.machine count).memory call.sourceId qEntry first.tree
      let memory := StackPopRelease.commitTree middle call.returnId bEntry second.tree
      obtain ⟨plan,runtime,complete,shape,capacity,rights⟩ := CurrentCallRootRelease.different_trees_plan raw.output.child.tree out.updated.extra global
        (S05ConcreteProtectedChildCompletion.extend raw.sourcePrecise.completion raw.child raw.sourcePointer.grant) completion
        qRes.1 bRes.1 qRes.2.1 bRes.2.1 qRes.2.2.1 bRes.2.2.1 call.sourceId call.returnId (Ne.symm same) frame
        raw.child out.borrowed.child raw.returnPointer.grant qNode bNode qAt bAt qHidden bHidden frameTags boolHidden bRes.2.2.2.2
        (UInt64.ofNat call.sourceOffset) len (UInt64.ofNat call.returnOffset) qPositive bPositive qActive bActive qOwned bOwned
        qRes.2.2.2 bRes.2.2.2.1 (out.machine count).memory qEntry bEntry qLive bLive qExtra rfl
      exact ⟨memory,second.tree,plan,StackPopRelease.lookup_commit_same middle call.returnId bEntry second.tree,runtime,complete,shape,capacity,rights⟩
  obtain ⟨memory,finalTree,plan,finalLive,runtime,complete,shape,capacity,rights⟩ := output
  let current : MachineHooks.BorrowState := ⟨global,tracker.retagMode⟩
  let final := ActualPopPlan.released (out.machine count) memory current frame
  obtain ⟨initial,idEq,pointerEq,offsetEq,binding⟩ := CurrentCallRootPhysicalWindow.of_entry out count facts
  obtain ⟨window,ptrSame,idSame,offsetSame,finalBinding⟩ := CurrentCallRootPhysicalWindow.plan global.protectedTags frame.protectedTags.toList
    (out.machine count).memory memory plan (out.machine count) final rfl rfl rfl place initial binding
  have finalId : window.id = call.returnId := idSame.trans idEq
  have finalPtr : window.pointer = raw.returnPointer.value := ptrSame.trans pointerEq
  have finalOffset : window.offset = UInt64.ofNat call.returnOffset := offsetSame.trans offsetEq
  have entryEq : window.entry = {bEntry with allocation := bEntry.allocation.setExtra finalTree} := by
    have live := window.live
    rw [finalId] at live
    exact (Prod.mk.inj (Option.some.inj (live.symm.trans finalLive))).2
  have treeEq : window.entry.allocation.extra = finalTree := by rw [entryEq];rfl
  obtain ⟨node,nodeAt,provenance⟩ := CurrentCallEntryProtectionData.Facts.original_return_node facts
  have nodes : finalTree.nodes = out.updated.extra.nodes := by rw [shape]
  have finalOrder := GeneralBorrowParentTagInvariant.nodes_frame out.updated.extra finalTree nodes bRes.2.2.1
  have bound : (UInt64.ofNat call.returnOffset).toNat+1 ≤ finalTree.locations.size.bytes.toNat := by
    rw [capacity,facts.extra,facts.written.capacity,out.borrowed.metadata.capacity]
    exact endpoints.2.2.2.2.1
  refine ⟨{
    memory := memory
    plan := plan
    window := window
    binding := finalBinding
    roleId := finalId
    roleOffset := finalOffset
    rolePointer := finalPtr
    completion := completion
    runtime := ?_
    completes := ?_
    order := ?_
    short := ?_
    node := node
    present := ?_
    provenance := ?_
    bounds := ?_
    owned := ?_ }⟩
  · rw [treeEq];exact runtime
  · rw [treeEq];exact complete
  · rw [treeEq];exact finalOrder
  · rw [treeEq,nodes];exact bRes.2.2.2.1
  · change window.entry.allocation.extra.nodes.get raw.returnPointer.grant = some node
    rw [treeEq,nodes];exact nodeAt
  · rw [finalPtr];exact provenance
  · rw [treeEq,finalOffset];exact bound
  · rw [treeEq,finalOffset];exact rights

end
end DuplicatePrefix.CurrentCallEntryRootRelease
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallEntryRootRelease." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved entry root release dependency {dependency}"
