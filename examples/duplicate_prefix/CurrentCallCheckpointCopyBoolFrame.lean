import duplicate_prefix.CurrentCallCheckpointAcceptedBoolCurrent
import duplicate_prefix.CurrentCallCheckpointCopyPrefix
import duplicate_prefix.CurrentCallResourceCopyActivity
import duplicate_prefix.GeneralBorrowRangeOutsideOwned
import duplicate_prefix.CurrentCallSpatialSubrangeSequence
namespace DuplicatePrefix.CurrentCallCheckpointCopyBoolFrame
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallPostEntryCheckpoint GeneralRangeMapOrigins S05CompletedAncestryReadMutable
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- One actual ranged copy access retains the independent Bool bank and
its quiet-leaf activity. The source contributes physical capabilities only. -/
theorem access (tree : BorrowTree) (global : GlobalState) (C : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (parents : ParentInterpretation tree C)
    (tag : BorTag) (source target : UniIndex) (sourceNode targetNode : TreeNode)
    (sourceAt : tree.nodeAt source=some sourceNode) (mapped : tree.indexOfTag tag=some source)
    (targetAt : tree.nodeAt target=some targetNode) (leaf : targetNode.children=#[]) (hidden : targetNode.isExposed=false)
    (different : target≠source) (start amount lower upper : UInt64) (kind : AccessKind)
    (bounds : start.toNat+amount.toNat≤tree.locations.size.bytes.toNat)
    (normal : OwnedOn (fun location=>Nonempty (DuplicatePrefixNormalKind.Capability tree location global.protectedTags source kind))
      start (start+amount) tree.locations)
    (apart : ∀point : UInt64,lower.toNat≤point.toNat→point.toNat<upper.toNat→point.toNat<start.toNat∨(start+amount).toNat≤point.toNat)
    (owned : OwnedOn (Authority tree C global.protectedTags target) lower upper tree.locations)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write lower upper)
    (shape : (tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes start) (Size.ofBytes amount) kind global.protectedTags
      .VisitChildrenOfAccessed).tree={tree with locations:=(tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes start) (Size.ofBytes amount)
        kind global.protectedTags .VisitChildrenOfAccessed).tree.locations}) :
    let after:=(tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes start) (Size.ofBytes amount) kind global.protectedTags .VisitChildrenOfAccessed).tree
    ParentInterpretation after C ∧OwnedOn (Authority after C global.protectedTags target) lower upper after.locations ∧
      after.nodeAt target=some targetNode ∧GeneralBorrowFreshActiveWithin.ActiveWithin after target .Write lower upper := by
  have nodes:=congrArg BorrowTree.nodes shape
  have retained:=GeneralBorrowRangeOutsideOwned.owned (Authority tree C global.protectedTags target) tree (.concrete tag)
    (Size.ofBytes start) (Size.ofBytes amount) kind global.protectedTags .VisitChildrenOfAccessed runtime.formed.well bounds lower upper apart owned
  refine ⟨?_,?_,?_,?_⟩
  · rw [shape]
    exact CurrentCallCheckpointSharedBoolFrame.parents_locations tree C parents _
  · intro cursor valid positive begin finish index node found
    rw [nodes] at found
    exact retained cursor valid positive begin finish index node found
  · change (tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes start) (Size.ofBytes amount) kind global.protectedTags .VisitChildrenOfAccessed).tree.nodes.get target=some targetNode
    rw [nodes]
    exact targetAt
  · exact CurrentCallResourceCopyActivity.concrete_of_normal tree global runtime tag source target sourceNode sourceAt start amount kind bounds normal mapped
      targetNode targetAt leaf hidden different lower upper active .VisitChildrenOfAccessed

/-- A request subwindow uses physical Normal capabilities from the unchanged
full spatial bank. Each row keeps its fixed original cell interpretation. -/
theorem normal_kind {before tracker ctx offset length}
    (role : CurrentCallSpatialCover.RoleCover before tracker ctx .mut offset length)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (tag : BorTag) (source : UniIndex) (concrete : role.family.value.provenance=.concrete role.backing.id tag)
    (mapped : role.backing.allocation.extra.indexOfTag tag=some source)
    (wholeStart wholeAmount start amount : UInt64) (startEq : wholeStart.toNat=offset) (amountEq : wholeAmount.toNat=length)
    (bounds : wholeStart.toNat+wholeAmount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat)
    (lower : wholeStart.toNat≤start.toNat) (upper : start.toNat+amount.toNat≤wholeStart.toNat+wholeAmount.toNat)
    (kind : AccessKind) :
    OwnedOn (fun location=>Nonempty (DuplicatePrefixNormalKind.Capability role.backing.allocation.extra location tracker.global.protectedTags source kind))
      start (start+amount) role.backing.allocation.extra.locations := by
  have whole:=CurrentCallCheckpointMutableBoolFrame.spatial_normal role runtime tag source concrete mapped wholeStart wholeAmount startEq amountEq bounds
  have wholeStop : (wholeStart+wholeAmount).toNat=wholeStart.toNat+wholeAmount.toNat:=by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt bounds role.backing.allocation.extra.locations.size.bytes.toNat_lt)]
  have requestStop : (start+amount).toNat=start.toNat+amount.toNat:=by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_trans upper bounds) role.backing.allocation.extra.locations.size.bytes.toNat_lt)]
  intro cursor valid positive beforeUpper afterLower
  obtain ⟨normal⟩:=whole cursor valid (by rw [wholeStop];rw [requestStop] at positive;omega)
    (by rw [wholeStop];rw [requestStop] at beforeUpper;omega) (by omega)
  exact ⟨DuplicatePrefixNormalKind.of_normal _ _ _ _ normal kind⟩


/-- The two actual source-prefix accesses retain the Bool bank while the
source ReadStage keeps its complete original role bank for the second fold. -/
theorem two {before tracker ctx offset length}
    (role : CurrentCallSpatialCover.RoleCover before tracker ctx .mut offset length)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (readStart readAmount writeStart writeAmount wholeStart wholeAmount : UInt64)
    (stage : CurrentCallSpatialSubrangeSequence.ReadStage role entry readStart readAmount)
    (C : Completion) (parents : ParentInterpretation role.backing.allocation.extra C)
    (tag : BorTag) (source target : UniIndex) (sourceNode targetNode : TreeNode)
    (concrete : role.family.value.provenance=.concrete role.backing.id tag)
    (sourceAt : role.backing.allocation.extra.nodeAt source=some sourceNode)
    (mapped : role.backing.allocation.extra.indexOfTag tag=some source)
    (targetAt : role.backing.allocation.extra.nodeAt target=some targetNode)
    (leaf : targetNode.children=#[]) (hidden : targetNode.isExposed=false) (different : target≠source)
    (startEq : wholeStart.toNat=offset) (amountEq : wholeAmount.toNat=length)
    (bounds : wholeStart.toNat+wholeAmount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat)
    (readLower : wholeStart.toNat≤readStart.toNat) (readUpper : readStart.toNat+readAmount.toNat≤wholeStart.toNat+wholeAmount.toNat)
    (writeLower : wholeStart.toNat≤writeStart.toNat) (writeUpper : writeStart.toNat+writeAmount.toNat≤wholeStart.toNat+wholeAmount.toNat)
    (lower upper : UInt64)
    (readApart : ∀point : UInt64,lower.toNat≤point.toNat→point.toNat<upper.toNat→point.toNat<readStart.toNat∨(readStart+readAmount).toNat≤point.toNat)
    (writeApart : ∀point : UInt64,lower.toNat≤point.toNat→point.toNat<upper.toNat→point.toNat<writeStart.toNat∨(writeStart+writeAmount).toNat≤point.toNat)
    (owned : OwnedOn (Authority role.backing.allocation.extra C tracker.global.protectedTags target) lower upper role.backing.allocation.extra.locations)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin role.backing.allocation.extra target .Write lower upper)
    (writeShape : (CurrentCallSpatialSubrangeSequence.ReadStage.writeResult stage writeStart writeAmount).tree=
      {stage.current.backing.allocation.extra with locations:=(CurrentCallSpatialSubrangeSequence.ReadStage.writeResult stage writeStart writeAmount).tree.locations}) :
    let actual:=(CurrentCallSpatialSubrangeSequence.ReadStage.writeResult stage writeStart writeAmount).tree
    ParentInterpretation actual C ∧OwnedOn (Authority actual C tracker.global.protectedTags target) lower upper actual.locations ∧
      actual.nodeAt target=some targetNode ∧GeneralBorrowFreshActiveWithin.ActiveWithin actual target .Write lower upper := by
  have readConcrete : CurrentCallSpatialRows.provenance role=.concrete tag:=by unfold CurrentCallSpatialRows.provenance;rw [concrete]
  have readShape:=stage.shape
  simp only [CurrentCallSpatialSubrangeSequence.readResult,readConcrete] at readShape
  have readNormal:=normal_kind role runtime tag source concrete mapped wholeStart wholeAmount readStart readAmount startEq amountEq bounds readLower readUpper .Read
  obtain ⟨readParents,readOwned,readAt,readActive⟩:=access role.backing.allocation.extra tracker.global C runtime parents tag source target sourceNode targetNode
    sourceAt mapped targetAt leaf hidden different readStart readAmount lower upper .Read (Nat.le_trans readUpper bounds) readNormal readApart owned active readShape
  have stageTree:=CurrentCallSpatialSubrangeSequence.ReadStage.tree stage
  simp only [CurrentCallSpatialSubrangeSequence.readResult,readConcrete] at stageTree
  have concreteAfter : stage.current.family.value.provenance=.concrete stage.current.backing.id tag:=by rw [stage.family,stage.id];exact concrete
  have sourceAfter : stage.current.backing.allocation.extra.nodeAt source=some sourceNode:=by rw [stageTree,readShape];exact sourceAt
  have mappedAfter : stage.current.backing.allocation.extra.indexOfTag tag=some source:=by rw [stageTree,readShape];exact mapped
  have targetAfter : stage.current.backing.allocation.extra.nodeAt target=some targetNode:=by rw [stageTree];exact readAt
  have boundsAfter : wholeStart.toNat+wholeAmount.toNat≤stage.current.backing.allocation.extra.locations.size.bytes.toNat:=by
    rw [CurrentCallSpatialSubrangeSequence.ReadStage.tree stage,stage.capacity];exact bounds
  have writeNormal:=normal_kind stage.current stage.runtime tag source concreteAfter mappedAfter wholeStart wholeAmount writeStart writeAmount
    startEq amountEq boundsAfter writeLower writeUpper .Write
  have stageParents : ParentInterpretation stage.current.backing.allocation.extra C:=by rw [stageTree];exact readParents
  have stageOwned : OwnedOn (Authority stage.current.backing.allocation.extra C tracker.global.protectedTags target) lower upper stage.current.backing.allocation.extra.locations:=by
    rw [stageTree];exact readOwned
  have stageActive : GeneralBorrowFreshActiveWithin.ActiveWithin stage.current.backing.allocation.extra target .Write lower upper:=by rw [stageTree];exact readActive
  have writeConcrete : CurrentCallSpatialRows.provenance stage.current=.concrete tag:=by unfold CurrentCallSpatialRows.provenance;rw [concreteAfter]
  have literalShape:=writeShape
  simp only [CurrentCallSpatialSubrangeSequence.ReadStage.writeResult,writeConcrete] at literalShape
  have retained:=access stage.current.backing.allocation.extra tracker.global C stage.runtime stageParents tag source target sourceNode targetNode
    sourceAfter mappedAfter targetAfter leaf hidden different writeStart writeAmount lower upper .Write (Nat.le_trans writeUpper boundsAfter)
    writeNormal writeApart stageOwned stageActive literalShape
  simpa only [CurrentCallSpatialSubrangeSequence.ReadStage.writeResult,writeConcrete] using retained

end
end DuplicatePrefix.CurrentCallCheckpointCopyBoolFrame
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointCopyBoolFrame" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual copy Bool frame dependency {dependency}"
