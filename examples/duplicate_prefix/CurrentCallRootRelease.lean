import duplicate_prefix.S04ReturnBorrowBridge
import duplicate_prefix.S05CurrentMutableProtectorRelease
import duplicate_prefix.S05CompletedChildReanchor
import duplicate_prefix.CandidateCurrentWindowAuthority
import duplicate_prefix.S05WildcardCompletedWrite
import duplicate_prefix.S05CompletedAncestryRangeWrite
namespace DuplicatePrefix.CurrentCallRootRelease
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowProjection GeneralRangeMapOrigins
open S05CompletedAncestryReadMutable (Authority)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
noncomputable section

/-- Both root protectors release under the SAME current global flags. Only
then does actual whole-frame endCall restore the original Bool grant. -/
theorem same_tree (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (allocation : AllocId) (frame : FrameState) (q b original : UniIndex) (qNode bNode : TreeNode)
    (qAt : tree.nodeAt q = some qNode) (bAt : tree.nodeAt b = some bNode)
    (qHidden : qNode.isExposed = false) (bHidden : bNode.isExposed = false) (bLeaf : bNode.children = #[])
    (different : b ≠ q)
    (ownedFrame : frame.protectedTags = #[(allocation,qNode.tag),(allocation,bNode.tag)])
    (edge : completion.parents[b.toNat]? = some (some original))
    (offset len boolOffset : UInt64)
    (positive : offset.toNat < (offset+len).toNat) (boolPositive : boolOffset.toNat < (boolOffset+1).toNat)
    (disjoint : (offset+len).toNat ≤ boolOffset.toNat ∨ (boolOffset+1).toNat ≤ offset.toNat)
    (qActive : GeneralBorrowFreshActiveWithin.ActiveWithin tree q .Write offset (offset+len))
    (bActive : GeneralBorrowFreshActiveWithin.ActiveWithin tree b .Write boolOffset (boolOffset+1))
    (qOwned : OwnedOn (Authority tree completion global.protectedTags q) offset (offset+len) tree.locations)
    (bOwned : OwnedOn (Authority tree completion global.protectedTags b) boolOffset (boolOffset+1) tree.locations)
    (short : tree.nodes.size < 65536) :
    let first := tree.releaseProtector qNode.tag global.protectedTags
    let second := first.tree.releaseProtector bNode.tag global.protectedTags
    first.status = .Released ∧ second.status = .Released ∧
      DuplicatePrefixBorrowContract.RuntimeFacts second.tree (global.endCall frame) ∧ Completes second.tree completion ∧
      second.tree = {tree with locations := second.tree.locations} ∧ second.tree.locations.size = tree.locations.size ∧
      OwnedOn (Authority second.tree completion (global.endCall frame).protectedTags original)
        boolOffset (boolOffset+1) second.tree.locations := by
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path tree runtime.formed.toGraphState q qNode qAt
  obtain ⟨qDone,qFrame,qRuntime,qComplete,qCapacity,boolAfter,bActiveAfter⟩ :=
    S05CurrentMutableProtectorRelease.release_preserving_disjoint_activity tree global completion runtime complete order position root q rootNode qNode
      slot rootAt path qAt qHidden offset len positive qActive qOwned boolOffset (boolOffset+1) boolPositive
      (Authority tree completion global.protectedTags b) disjoint bOwned b bNode bAt bLeaf bHidden different bActive short
  let first := tree.releaseProtector qNode.tag global.protectedTags
  have qNodes : first.tree.nodes = tree.nodes := by rw [qFrame]
  have bAtAfter : first.tree.nodeAt b = some bNode := by change first.tree.nodes.get b = some bNode;rw [qNodes];exact bAt
  have bOwnedAfter : OwnedOn (Authority first.tree completion global.protectedTags b) boolOffset (boolOffset+1) first.tree.locations := by
    rw [qFrame]
    intro cursor valid nonzero start stop index node present
    exact boolAfter cursor valid nonzero start stop index node present
  obtain ⟨bp,br,brNode,bslot,brAt,bpath⟩ := CandidateCurrentWindowAuthority.root_path first.tree qRuntime.formed.toGraphState b bNode bAtAfter
  have afterOrder := GeneralBorrowParentTagInvariant.nodes_frame tree first.tree qNodes order
  obtain ⟨bDone,bFrame,bRuntime,bComplete,bCapacity,bOwn⟩ := S05CurrentMutableProtectorRelease.release_owned first.tree global completion
    qRuntime qComplete afterOrder bp br b brNode bNode bslot brAt bpath bAtAfter bHidden boolOffset 1 boolPositive bActiveAfter bOwnedAfter
    (by rw [qNodes];exact short)
  let second := first.tree.releaseProtector bNode.tag global.protectedTags
  have bNodes : second.tree.nodes = tree.nodes := by rw [bFrame,qNodes]
  have finalQ : second.tree.nodeAt q = some qNode := by change second.tree.nodes.get q = some qNode;rw [bNodes];exact qAt
  have finalB : second.tree.nodeAt b = some bNode := by change second.tree.nodes.get b = some bNode;rw [bNodes];exact bAt
  have hiddenFrame : S04ReturnReleaseParent.HiddenFrame second.tree frame := by
    intro row member index node present sameTag
    rw [ownedFrame] at member
    change row ∈ [(allocation,qNode.tag),(allocation,bNode.tag)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same
    · subst row
      have one := bRuntime.formed.allocator.nodeTags index node present
      have two := bRuntime.formed.allocator.nodeTags q qNode finalQ
      rw [sameTag,two] at one
      have same := Option.some.inj one
      subst index
      have nodeEq := Option.some.inj (present.symm.trans finalQ)
      subst node;exact qHidden
    · subst row
      have one := bRuntime.formed.allocator.nodeTags index node present
      have two := bRuntime.formed.allocator.nodeTags b bNode finalB
      rw [sameTag,two] at one
      have same := Option.some.inj one
      subst index
      have nodeEq := Option.some.inj (present.symm.trans finalB)
      subst node;exact bHidden
  have afterRuntime := S05CompletedChildReanchor.runtime_end_call second.tree global frame bRuntime hiddenFrame
  have oldOwned := S05CompletedChildReanchor.owned_end_call second.tree completion global frame allocation b original bNode
    boolOffset (boolOffset+1) edge finalB (by rw [ownedFrame];simp) bOwn
  have finalFrame : second.tree = {tree with locations := second.tree.locations} := by
    rw [bFrame,qFrame]
  exact ⟨qDone,bDone,afterRuntime,bComplete,finalFrame,bCapacity.trans qCapacity,oldOwned⟩
theorem same_tree_plan (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (allocation : AllocId) (frame : FrameState) (q b original : UniIndex) (qNode bNode : TreeNode)
    (qAt : tree.nodeAt q = some qNode) (bAt : tree.nodeAt b = some bNode)
    (qHidden : qNode.isExposed = false) (bHidden : bNode.isExposed = false) (bLeaf : bNode.children = #[])
    (different : b ≠ q)
    (ownedFrame : frame.protectedTags = #[(allocation,qNode.tag),(allocation,bNode.tag)])
    (edge : completion.parents[b.toNat]? = some (some original))
    (offset len boolOffset : UInt64)
    (positive : offset.toNat < (offset+len).toNat) (boolPositive : boolOffset.toNat < (boolOffset+1).toNat)
    (disjoint : (offset+len).toNat ≤ boolOffset.toNat ∨ (boolOffset+1).toNat ≤ offset.toNat)
    (qActive : GeneralBorrowFreshActiveWithin.ActiveWithin tree q .Write offset (offset+len))
    (bActive : GeneralBorrowFreshActiveWithin.ActiveWithin tree b .Write boolOffset (boolOffset+1))
    (qOwned : OwnedOn (Authority tree completion global.protectedTags q) offset (offset+len) tree.locations)
    (bOwned : OwnedOn (Authority tree completion global.protectedTags b) boolOffset (boolOffset+1) tree.locations)
    (short : tree.nodes.size < 65536)
    (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : memory.live.find? (fun row => row.1 == allocation) = some (allocation,entry))
    (extra : entry.allocation.extra = tree) :
    let first := tree.releaseProtector qNode.tag global.protectedTags
    let second := first.tree.releaseProtector bNode.tag global.protectedTags
    let middle := StackPopRelease.commitTree memory allocation entry first.tree
    let middleEntry := {entry with allocation := entry.allocation.setExtra first.tree}
    let final := StackPopRelease.commitTree middle allocation middleEntry second.tree
    StackPopRelease.Plan global.protectedTags frame.protectedTags.toList memory final ∧
      DuplicatePrefixBorrowContract.RuntimeFacts second.tree (global.endCall frame) ∧ Completes second.tree completion ∧
      second.tree = {tree with locations := second.tree.locations} ∧ second.tree.locations.size = tree.locations.size ∧
      OwnedOn (Authority second.tree completion (global.endCall frame).protectedTags original)
        boolOffset (boolOffset+1) second.tree.locations := by
  obtain ⟨qDone,bDone,runtimeAfter,completeAfter,frameAfter,capacity,owned⟩ := same_tree tree global completion runtime complete order
    allocation frame q b original qNode bNode qAt bAt qHidden bHidden bLeaf different ownedFrame edge offset len boolOffset
    positive boolPositive disjoint qActive bActive qOwned bOwned short
  let first := tree.releaseProtector qNode.tag global.protectedTags
  let second := first.tree.releaseProtector bNode.tag global.protectedTags
  have firstEq : entry.allocation.extra.releaseProtector qNode.tag global.protectedTags = ⟨first.tree,.Released⟩ := by
    rw [extra]
    change first = ⟨first.tree,.Released⟩
    have eta : first = ⟨first.tree,first.status⟩ := by cases first;rfl
    rw [show first.status = .Released from qDone] at eta
    exact eta
  let middle := StackPopRelease.commitTree memory allocation entry first.tree
  let middleEntry := {entry with allocation := entry.allocation.setExtra first.tree}
  have secondEq : middleEntry.allocation.extra.releaseProtector bNode.tag global.protectedTags = ⟨second.tree,.Released⟩ := by
    change first.tree.releaseProtector bNode.tag global.protectedTags = _
    change second = ⟨second.tree,.Released⟩
    have eta : second = ⟨second.tree,second.status⟩ := by cases second;rfl
    rw [show second.status = .Released from bDone] at eta
    exact eta
  refine ⟨?_,runtimeAfter,completeAfter,frameAfter,capacity,owned⟩
  rw [ownedFrame]
  exact StackPopRelease.Plan.live allocation qNode.tag entry first.tree [(allocation,bNode.tag)] memory _ live firstEq
    (StackPopRelease.Plan.live allocation bNode.tag middleEntry second.tree [] middle _
      (StackPopRelease.lookup_commit_same memory allocation entry first.tree) secondEq (StackPopRelease.Plan.nil _))

/-- Distinct allocations still use one current protector table through BOTH
releases. The original Bool grant is reanchored only after whole-frame removal. -/
theorem different_trees_plan (sourceTree boolTree : BorrowTree) (global : GlobalState)
    (sourceCompletion boolCompletion : Completion)
    (sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts sourceTree global)
    (boolRuntime : DuplicatePrefixBorrowContract.RuntimeFacts boolTree global)
    (sourceComplete : Completes sourceTree sourceCompletion) (boolComplete : Completes boolTree boolCompletion)
    (sourceOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder sourceTree)
    (boolOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder boolTree)
    (sourceId boolId : AllocId) (different : boolId ≠ sourceId) (frame : FrameState)
    (q b original : UniIndex) (qNode bNode : TreeNode)
    (qAt : sourceTree.nodeAt q = some qNode) (bAt : boolTree.nodeAt b = some bNode)
    (qHidden : qNode.isExposed = false) (bHidden : bNode.isExposed = false)
    (ownedFrame : frame.protectedTags = #[(sourceId,qNode.tag),(boolId,bNode.tag)])
    (hiddenFrame : S04ReturnReleaseParent.HiddenFrame boolTree frame)
    (edge : boolCompletion.parents[b.toNat]? = some (some original))
    (offset len boolOffset : UInt64)
    (positive : offset.toNat < (offset+len).toNat) (boolPositive : boolOffset.toNat < (boolOffset+1).toNat)
    (qActive : GeneralBorrowFreshActiveWithin.ActiveWithin sourceTree q .Write offset (offset+len))
    (bActive : GeneralBorrowFreshActiveWithin.ActiveWithin boolTree b .Write boolOffset (boolOffset+1))
    (qOwned : OwnedOn (Authority sourceTree sourceCompletion global.protectedTags q) offset (offset+len) sourceTree.locations)
    (bOwned : OwnedOn (Authority boolTree boolCompletion global.protectedTags b) boolOffset (boolOffset+1) boolTree.locations)
    (qShort : sourceTree.nodes.size < 65536) (bShort : boolTree.nodes.size < 65536)
    (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (sourceEntry boolEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceLive : memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,sourceEntry))
    (boolLive : memory.live.find? (fun row => row.1 == boolId) = some (boolId,boolEntry))
    (sourceExtra : sourceEntry.allocation.extra = sourceTree) (boolExtra : boolEntry.allocation.extra = boolTree) :
    let first := sourceTree.releaseProtector qNode.tag global.protectedTags
    let second := boolTree.releaseProtector bNode.tag global.protectedTags
    let middle := StackPopRelease.commitTree memory sourceId sourceEntry first.tree
    let final := StackPopRelease.commitTree middle boolId boolEntry second.tree
    StackPopRelease.Plan global.protectedTags frame.protectedTags.toList memory final ∧
      DuplicatePrefixBorrowContract.RuntimeFacts second.tree (global.endCall frame) ∧ Completes second.tree boolCompletion ∧
      second.tree = {boolTree with locations := second.tree.locations} ∧ second.tree.locations.size = boolTree.locations.size ∧
      OwnedOn (Authority second.tree boolCompletion (global.endCall frame).protectedTags original)
        boolOffset (boolOffset+1) second.tree.locations := by
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path sourceTree sourceRuntime.formed.toGraphState q qNode qAt
  obtain ⟨qDone,_,_,_,_⟩ := S05CurrentMutableProtectorRelease.release_runtime sourceTree global sourceCompletion sourceRuntime sourceComplete
    sourceOrder position root q rootNode qNode slot rootAt path qAt qHidden offset len positive qActive qOwned qShort
  obtain ⟨bp,br,brNode,bslot,brAt,bpath⟩ := CandidateCurrentWindowAuthority.root_path boolTree boolRuntime.formed.toGraphState b bNode bAt
  obtain ⟨bDone,bFrame,bRuntime,bComplete,bCapacity,bOwn⟩ := S05CurrentMutableProtectorRelease.release_owned boolTree global boolCompletion boolRuntime
    boolComplete boolOrder bp br b brNode bNode bslot brAt bpath bAt bHidden boolOffset 1 boolPositive bActive bOwned bShort
  let first := sourceTree.releaseProtector qNode.tag global.protectedTags
  let second := boolTree.releaseProtector bNode.tag global.protectedTags
  have finalB : second.tree.nodeAt b = some bNode := by change second.tree.nodes.get b = some bNode;rw [bFrame];exact bAt
  have finalHidden : S04ReturnReleaseParent.HiddenFrame second.tree frame := by
    intro row member index node found tag
    apply hiddenFrame row member index node _ tag
    change second.tree.nodes.get index = some node at found
    rw [bFrame] at found
    exact found
  have afterRuntime := S05CompletedChildReanchor.runtime_end_call second.tree global frame bRuntime finalHidden
  have oldOwned := S05CompletedChildReanchor.owned_end_call second.tree boolCompletion global frame boolId b original bNode
    boolOffset (boolOffset+1) edge finalB (by rw [ownedFrame];simp) bOwn
  have firstEq : sourceEntry.allocation.extra.releaseProtector qNode.tag global.protectedTags = ⟨first.tree,.Released⟩ := by
    rw [sourceExtra]
    change first = ⟨first.tree,.Released⟩
    have eta : first = ⟨first.tree,first.status⟩ := by cases first;rfl
    rw [show first.status = .Released from qDone] at eta
    exact eta
  have secondEq : boolEntry.allocation.extra.releaseProtector bNode.tag global.protectedTags = ⟨second.tree,.Released⟩ := by
    rw [boolExtra]
    change second = ⟨second.tree,.Released⟩
    have eta : second = ⟨second.tree,second.status⟩ := by cases second;rfl
    rw [show second.status = .Released from bDone] at eta
    exact eta
  refine ⟨?_,afterRuntime,bComplete,bFrame,bCapacity,oldOwned⟩
  rw [ownedFrame]
  exact StackPopRelease.Plan.live sourceId qNode.tag sourceEntry first.tree [(boolId,bNode.tag)] memory _ sourceLive firstEq
    (StackPopRelease.Plan.live boolId bNode.tag boolEntry second.tree [] _ _
      (StackPopRelease.lookup_commit_other memory sourceId boolId sourceEntry boolEntry first.tree different boolLive)
      secondEq (StackPopRelease.Plan.nil _))

/-- The final borrow Write uses the ORIGINAL pointer provenance. Wildcards
execute the true all-root source-none/max-none operation. -/
theorem write_original (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (original : UniIndex) (node : TreeNode) (present : tree.nodeAt original = some node)
    (provenance : Provenance)
    (binds : match provenance with | .concrete _ tag => tag = node.tag | .wildcard => node.isExposed = true)
    (offset : UInt64) (bounds : offset.toNat+1 ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags original) offset (offset+1) tree.locations)
    (short : tree.nodes.size < 65536) :
    (tree.performBorrowAccessRange (S04ReturnBorrowBridge.extra provenance) (Size.ofBytes offset) (Size.ofBytes 1)
      .Write global.protectedTags .VisitChildrenOfAccessed).status = .Completed := by
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path tree runtime.formed.toGraphState original node present
  obtain ⟨depth⟩ := runtime.formed.depth
  have initial : OwnedOn (fun location => GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
      Authority tree completion global.protectedTags original location) offset (offset+1) tree.locations := by
    intro cursor valid positive start stop
    exact ⟨runtime.possible cursor valid,owned cursor valid positive start stop⟩
  cases provenance with
  | concrete id tag =>
    have tagEq : tag = node.tag := binds
    subst tag
    exact (S05CompletedAncestryRangeWrite.access tree completion global.protectedTags complete runtime.formed.toGraphState
      depth order position root original rootNode node slot rootAt present path (Size.ofBytes offset) (Size.ofBytes 1)
      offset (offset+1) initial runtime.formed.well
      (fun cursor valid => ⟨runtime.coherent cursor valid,runtime.formed.profile cursor valid⟩)
      bounds (Nat.le_refl _) (Nat.le_refl _) short .VisitChildrenOfAccessed).completed
  | wildcard =>
    exact (S05WildcardCompletedWrite.range tree completion global.protectedTags complete runtime.formed.toGraphState depth order position root original
      rootNode node slot rootAt present binds path (Size.ofBytes offset) (Size.ofBytes 1) offset (offset+1) initial runtime.formed.well
      (fun cursor valid => ⟨runtime.coherent cursor valid,runtime.formed.profile cursor valid,runtime.possible cursor valid⟩)
      bounds (Nat.le_refl _) (Nat.le_refl _) short .VisitChildrenOfAccessed).completed

end
end DuplicatePrefix.CurrentCallRootRelease
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallRootRelease." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved root release dependency {dependency}"
