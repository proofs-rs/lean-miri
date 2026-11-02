import duplicate_prefix.CurrentCallLenRootData
import duplicate_prefix.CurrentCallRootActivity
import duplicate_prefix.GeneralBorrowRangeOutsideOwned
import duplicate_prefix.PositiveRootCopyBounds
import duplicate_prefix.StackPopRelease
import duplicate_prefix.CandidateCurrentJointRawReplacement

namespace DuplicatePrefix.CurrentCallCopiedBoolData
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership GeneralBorrowProjection GeneralRangeMapOrigins GeneralRangeMapState
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality
open S05ConcreteProtectedChildCompletion CurrentCallLen
open S05CompletedAncestryReadMutable (Authority)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def read (tree : BorrowTree) (held : MachineHooks.BorrowState) (tag : BorTag) (offset count : UInt64) :=
  tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count) .Read held.global.protectedTags .VisitChildrenOfAccessed

def write (tree : BorrowTree) (held : MachineHooks.BorrowState) (tag : BorTag) (offset count : UInt64) :=
  (read tree held tag offset count).tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count)
    .Write held.global.protectedTags .VisitChildrenOfAccessed

private theorem replace_runtime (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (locations : DedupRangeMap LocationTree)
    (well : locations.WellFormed)
    (rows : Every (fun location => LocationCoherent tree location global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) locations) :
    DuplicatePrefixBorrowContract.RuntimeFacts {tree with locations := locations} global := by
  refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations tree locations runtime.formed.toGraphState,well⟩,?_⟩,
    ?_,?_,⟨runtime.below.mapping,runtime.below.protectors⟩⟩
  · intro index valid;exact ⟨(rows index valid).2.1.present,(rows index valid).2.1.vacant⟩
  · intro index valid;exact (rows index valid).1
  · intro index valid;exact (rows index valid).2.2

/-- The actual adjacent Read/Write copy retains the original Bool resource
record. Final source runtime and physical heap witnesses are retained outputs
of the actual copy; no Bool postrights or successful access is supplied. -/
theorem of_copy {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (held : MachineHooks.BorrowState) (completion : Completion)
    (boolData : CurrentCallLenRootData.Data s machine entry held completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra held.global)
    (complete : Completes entry.allocation.extra completion) (order : ParentTagOrder entry.allocation.extra)
    (source : UniIndex) (node : TreeNode) (present : entry.allocation.extra.nodeAt source = some node)
    (different : call.sourceId = call.returnId → s.out.borrowed.child ≠ source)
    (within : count≤len/2)
    (bounds : (UInt64.ofNat call.sourceOffset).toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (short : entry.allocation.extra.nodes.size<65536)
    (owned : OwnedOn (Authority entry.allocation.extra completion held.global.protectedTags source)
      (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) entry.allocation.extra.locations)
    (disjoint : call.sourceId = call.returnId →
      (UInt64.ofNat call.sourceOffset+len).toNat ≤ (UInt64.ofNat call.returnOffset).toNat ∨
      (UInt64.ofNat call.returnOffset+1).toNat ≤ (UInt64.ofNat call.sourceOffset).toNat)
    (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (afterEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (copiedExtra : afterEntry.allocation.extra = (write entry.allocation.extra held node.tag (UInt64.ofNat call.sourceOffset) count).tree)
    (postMemory : post.memory.live = (machine.memory.live.filter (fun row => row.1 != call.sourceId)).push (call.sourceId,afterEntry))
    (afterLive : post.memory.live.find? (fun row => row.1 == call.sourceId) = some (call.sourceId,afterEntry))
    (afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts afterEntry.allocation.extra held.global)
    (afterComplete : Completes afterEntry.allocation.extra completion) (afterOrder : ParentTagOrder afterEntry.allocation.extra)
    (afterNodes : afterEntry.allocation.extra.nodes = entry.allocation.extra.nodes)
    (afterCapacity : afterEntry.allocation.extra.locations.size = entry.allocation.extra.locations.size) :
    Nonempty (CurrentCallLenRootData.Data s post afterEntry held completion) := by
  by_cases same : call.sourceId = call.returnId
  · let offset := UInt64.ofNat call.sourceOffset
    let boolOffset := UInt64.ofNat call.returnOffset
    let accessed := read entry.allocation.extra held node.tag offset count
    have beforeEntryEq := boolData.sameEntry same
    have completionEq := boolData.sameCompletion same
    have bAt : entry.allocation.extra.nodeAt s.out.borrowed.child = some boolData.node := by simpa only [beforeEntryEq] using boolData.present
    have bOwned : OwnedOn (Authority entry.allocation.extra completion held.global.protectedTags s.out.borrowed.child)
        boolOffset (boolOffset+1) entry.allocation.extra.locations := by simpa only [beforeEntryEq,completionEq] using boolData.owned
    have bActive : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra s.out.borrowed.child .Write boolOffset (boolOffset+1) := by
      simpa only [beforeEntryEq] using boolData.active
    have sourceOwned : OwnedOn (Authority entry.allocation.extra completion held.global.protectedTags source)
        offset (offset+len) entry.allocation.extra.locations := owned
    have disjointHere : (offset+len).toNat ≤ boolOffset.toNat ∨ (boolOffset+1).toNat ≤ offset.toNat := disjoint same
    have numeric := PositiveRootCopyBounds.guarded len count offset entry.allocation.extra.locations.size.bytes within bounds
    have nowrap : offset.toNat+len.toNat<2^64 := Nat.lt_of_le_of_lt bounds entry.allocation.extra.locations.size.bytes.toNat_lt_size
    have sumEq : (offset+len).toNat = offset.toNat+len.toNat := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt nowrap]
    have firstNowrap : offset.toNat+count.toNat<2^64 := by omega
    have firstEq : (offset+count).toNat = offset.toNat+count.toNat := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt firstNowrap]
    have secondNowrap : (offset+count).toNat+count.toNat<2^64 := by omega
    have secondEq : (offset+count+count).toNat = offset.toNat+count.toNat+count.toNat := by
      rw [UInt64.toNat_add,Nat.mod_eq_of_lt secondNowrap,firstEq]
    obtain ⟨position,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path entry.allocation.extra runtime.formed.toGraphState source node present
    obtain ⟨depth⟩ := runtime.formed.depth
    have rows : OwnedOn (fun location => GeneralBorrowSnapshotReadRuntime.GlobalPossible entry.allocation.extra location ∧
        Authority entry.allocation.extra completion held.global.protectedTags source location) offset (offset+len) entry.allocation.extra.locations := by
      intro index valid positive start stop
      exact ⟨runtime.possible index valid,sourceOwned index valid positive start stop⟩
    have readContract := S05CompletedAncestryReadMutable.range entry.allocation.extra completion held.global.protectedTags complete runtime.formed.toGraphState depth order
      position root source rootNode node slot rootAt present path (Size.ofBytes offset) (Size.ofBytes count) offset (offset+len) rows runtime.formed.well
      (fun index valid=>⟨runtime.coherent index valid,runtime.formed.profile index valid,runtime.possible index valid⟩)
      numeric.2.2.1 (Nat.le_refl _) (by change (offset+count).toNat≤(offset+len).toNat;omega) short .VisitChildrenOfAccessed
    have readFrame : accessed.tree = {entry.allocation.extra with locations := accessed.tree.locations} := readContract.tree_eq
    have readNodes : accessed.tree.nodes = entry.allocation.extra.nodes := readContract.nodes
    have readRoots : accessed.tree.roots = entry.allocation.extra.roots := readContract.roots
    have readCapacity : accessed.tree.locations.size = entry.allocation.extra.locations.size := readContract.capacity
    have readRuntime : DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree held.global := by
      rw [readFrame]
      exact replace_runtime entry.allocation.extra held.global runtime accessed.tree.locations readContract.well readContract.runtime
    have readComplete : Completes accessed.tree completion := by
      rw [readFrame]
      exact CandidateCurrentJointRawReplacement.completes entry.allocation.extra completion _ complete
    have readOrder := GeneralBorrowParentTagInvariant.nodes_frame entry.allocation.extra accessed.tree readNodes order
    have readOwned : OwnedOn (Authority accessed.tree completion held.global.protectedTags source) offset (offset+len) accessed.tree.locations := by
      intro index valid positive start stop query current currentAt
      exact (readContract.rows index valid positive start stop).2 query current (by rw [readNodes] at currentAt;exact currentAt)
    have sourceAfter : accessed.tree.nodeAt source = some node := by change accessed.tree.nodes.get source = _;rw [readNodes];exact present
    have bAfter : accessed.tree.nodeAt s.out.borrowed.child = some boolData.node := by
      change accessed.tree.nodes.get s.out.borrowed.child = _
      rw [readNodes]
      exact bAt
    have rootAfter : accessed.tree.nodes.get root = some rootNode := by rw [readNodes];exact rootAt
    have slotAfter : accessed.tree.roots[position]? = some root := by rw [readRoots];exact slot
    have pathAfter : Path accessed.tree root source := GeneralBorrowPrimaryWitnessVisibility.path_nodes
      (before:=accessed.tree) (after:=entry.allocation.extra) readNodes.symm path
    have readSub : OwnedOn (Authority entry.allocation.extra completion held.global.protectedTags source) offset (offset+count) entry.allocation.extra.locations := by
      intro index valid positive start stop
      exact sourceOwned index valid (by omega) (by omega) stop
    have activeRead : GeneralBorrowFreshActiveWithin.ActiveWithin accessed.tree s.out.borrowed.child .Write boolOffset (boolOffset+1) :=
      CurrentCallRootActivity.concrete entry.allocation.extra held.global runtime completion complete position root source s.out.borrowed.child rootNode node
        slot rootAt present path node.tag ((complete.2.2.2.2.1 source node present).1) offset count numeric.2.2.1 readSub boolData.node bAt boolData.leaf boolData.hidden
        (different same) boolOffset (boolOffset+1) bActive .Read .VisitChildrenOfAccessed
    have writeBounds : (offset+count).toNat+count.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [readCapacity];omega
    have writeSub : OwnedOn (Authority accessed.tree completion held.global.protectedTags source) (offset+count) (offset+count+count) accessed.tree.locations := by
      intro index valid positive start stop
      exact readOwned index valid (by omega) (by omega) (by omega)
    have activeWrite : GeneralBorrowFreshActiveWithin.ActiveWithin (write entry.allocation.extra held node.tag offset count).tree s.out.borrowed.child .Write boolOffset (boolOffset+1) :=
      CurrentCallRootActivity.concrete accessed.tree held.global readRuntime completion readComplete position root source s.out.borrowed.child rootNode node
        slotAfter rootAfter sourceAfter pathAfter node.tag ((readComplete.2.2.2.2.1 source node sourceAfter).1) (offset+count) count writeBounds writeSub
        boolData.node bAfter boolData.leaf boolData.hidden (different same) boolOffset (boolOffset+1) activeRead .Write .VisitChildrenOfAccessed
    have outsideRead : ∀ point : UInt64, boolOffset.toNat ≤ point.toNat → point.toNat < (boolOffset+1).toNat →
        point.toNat < offset.toNat ∨ (offset+count).toNat ≤ point.toNat := by
      intro point start stop
      rcases disjointHere with left | right <;> omega
    have outsideWrite : ∀ point : UInt64, boolOffset.toNat ≤ point.toNat → point.toNat < (boolOffset+1).toNat →
        point.toNat < (offset+count).toNat ∨ (offset+count+count).toNat ≤ point.toNat := by
      intro point start stop
      rcases disjointHere with left | right <;> omega
    have readBool := GeneralBorrowRangeOutsideOwned.owned (Authority entry.allocation.extra completion held.global.protectedTags s.out.borrowed.child)
      entry.allocation.extra (.concrete node.tag) (Size.ofBytes offset) (Size.ofBytes count) .Read held.global.protectedTags .VisitChildrenOfAccessed
      runtime.formed.well numeric.2.2.1 boolOffset (boolOffset+1) outsideRead bOwned
    have writeBool := GeneralBorrowRangeOutsideOwned.owned (Authority entry.allocation.extra completion held.global.protectedTags s.out.borrowed.child)
      accessed.tree (.concrete node.tag) (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write held.global.protectedTags .VisitChildrenOfAccessed
      readRuntime.formed.well writeBounds boolOffset (boolOffset+1) outsideWrite readBool
    have finalOwned : OwnedOn (Authority afterEntry.allocation.extra completion held.global.protectedTags s.out.borrowed.child)
        boolOffset (boolOffset+1) afterEntry.allocation.extra.locations := by
      intro index valid positive start stop query current currentAt
      have retained : OwnedOn (Authority entry.allocation.extra completion held.global.protectedTags s.out.borrowed.child)
          boolOffset (boolOffset+1) afterEntry.allocation.extra.locations := by rw [copiedExtra];exact writeBool
      exact retained index valid positive start stop query current (by rw [afterNodes] at currentAt;exact currentAt)
    have finalAt : afterEntry.allocation.extra.nodeAt s.out.borrowed.child = some boolData.node := by
      change afterEntry.allocation.extra.nodes.get s.out.borrowed.child = _
      rw [afterNodes]
      exact bAt
    have finalOriginal : afterEntry.allocation.extra.nodeAt s.out.source.base.raw.returnPointer.grant = some boolData.originalNode := by
      change afterEntry.allocation.extra.nodes.get s.out.source.base.raw.returnPointer.grant = _
      rw [afterNodes]
      simpa only [beforeEntryEq,BorrowTree.nodeAt] using boolData.originalPresent
    have finalBounds : boolOffset.toNat+1 ≤ afterEntry.allocation.extra.locations.size.bytes.toNat := by
      rw [afterCapacity]
      simpa only [beforeEntryEq] using boolData.bounds
    have finalShort : afterEntry.allocation.extra.nodes.size<65536 := by rw [afterNodes];exact short
    have finalActive : GeneralBorrowFreshActiveWithin.ActiveWithin afterEntry.allocation.extra s.out.borrowed.child .Write boolOffset (boolOffset+1) := by
      rw [copiedExtra];exact activeWrite
    have finalEdge : completion.parents[s.out.borrowed.child.toNat]? = some (some s.out.source.base.raw.returnPointer.grant) := by
      simpa only [completionEq] using boolData.edge
    exact ⟨⟨afterEntry,completion,by simpa only [same] using afterLive,(fun _=>rfl),(fun _=>rfl),afterRuntime,afterComplete,afterOrder,finalShort,
      boolData.node,finalAt,boolData.tag,boolData.leaf,boolData.hidden,finalActive,finalOwned,finalEdge,
      boolData.originalNode,finalOriginal,boolData.originalProvenance,finalBounds,fun separate=>False.elim (separate same)⟩⟩
  · have boolLive : post.memory.live.find? (fun row => row.1 == call.returnId) = some (call.returnId,boolData.entry) := by
      rw [postMemory]
      have other := StackPopRelease.lookup_commit_other machine.memory call.sourceId call.returnId afterEntry boolData.entry afterEntry.allocation.extra (Ne.symm same) boolData.live
      simpa only [StackPopRelease.commitTree,Allocation.setExtra,Allocation.mapExtra] using other
    exact ⟨⟨boolData.entry,boolData.completion,boolLive,(fun equal=>False.elim (same equal)),(fun equal=>False.elim (same equal)),boolData.runtime,
      boolData.completes,boolData.order,boolData.short,boolData.node,boolData.present,boolData.tag,boolData.leaf,boolData.hidden,boolData.active,boolData.owned,boolData.edge,
      boolData.originalNode,boolData.originalPresent,boolData.originalProvenance,boolData.bounds,boolData.sourceAbsent⟩⟩

end
end DuplicatePrefix.CurrentCallCopiedBoolData
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallCopiedBoolData").length > 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved copied Bool data dependency {dependency}"
