import duplicate_prefix.S02WildcardSameDestinationRootOperation
import duplicate_prefix.GeneralBorrowRawWildcardFnEntryScopedResources
import duplicate_prefix.S02DisjointReadOnlyPositive
import duplicate_prefix.GeneralBorrowFreshRootScopedRange
namespace DuplicatePrefix.S02WildcardReturnSameSource
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixBorrowAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- Current disjoint source ownership survives the actual wildcard return
FnEntry and following concrete uninit Write. The output is the literal source
operation, with all completion and post-runtime facts derived internally. -/
theorem positive (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (offset : UInt64) (destination : Positive tree global.protectedTags none none none offset 1)
    (distinct : tree.roots.toList.Nodup) (headroom : tree.nodes.size+1 < 65536)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (source selected : Option UniIndex) (maximum : Option BorTag) (lower width : UInt64)
    (outside : offset.toNat+1 ≤ lower.toNat ∨ (lower+width).toNat ≤ offset.toNat)
    (old : Positive tree global.protectedTags source selected maximum lower width) :
    let registration := GeneralBorrowFnEntryRegistration.registered global frame allocation fresh
    let read := tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes 1)
      .Read registration.1.protectedTags .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes offset) .wildcard global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes 1) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    let written := child.tree.performBorrowAccessRange (.concrete global.nextPointerTag)
      (Size.ofBytes offset) (Size.ofBytes 1) .Write registration.1.protectedTags .VisitChildrenOfAccessed
    written.status = .Completed ∧
    Nonempty (Positive written.tree registration.1.protectedTags source selected maximum lower width) ∧
    DuplicatePrefixBorrowContract.RuntimeFacts written.tree registration.1 ∧
    written.tree.locations.size = tree.locations.size ∧
    (∀ query node,tree.nodeAt query = some node → written.tree.nodeAt query = some node) ∧
    (∀ tag query,tree.indexOfTag tag = some query → written.tree.indexOfTag tag = some query) := by
  dsimp only
  obtain ⟨output,actual,⟨sourceAfter⟩,capacity,oldNodes,oldTags⟩ :=
    S02WildcardSameDestinationRootOperation.operation_destination tree global frame allocation runtime offset 1 destination
      distinct (by omega) (by omega) fresh source selected maximum lower width (by simpa only [UInt64.toNat_one] using outside) old
  obtain ⟨same,actualSame,tag,globalEq,_frameEq,_readDone,_childDone,childRuntime,_childCapacity,growth,roots,
    child,tagged,_rootEq,⟨childPositive⟩,_activity,_geometry⟩ :=
    GeneralBorrowRawWildcardFnEntryScopedResources.invoke tree global frame allocation runtime offset 1 destination
      distinct (by omega) (by omega) fresh
  have equal : same = output := Except.ok.inj (actualSame.symm.trans actual)
  subst same
  have short : output.child.tree.nodes.size < 65536 := by omega
  obtain ⟨writeContract,writeRuntime,_childAfter⟩ := GeneralBorrowFreshRootScopedRange.access_runtime_kind
    output.child.tree output.global childRuntime output.tag child child output.tag tagged
    (Size.ofBytes offset) (Size.ofBytes 1) .Write .VisitChildrenOfAccessed offset 1 childPositive roots short
    (Nat.le_refl _) (Nat.le_refl _)
  have sourceWritten := S02DisjointReadOnlyPositive.positive_from_source_contract output.child.tree output.tag child child (some output.tag)
    tagged (Size.ofBytes offset) (Size.ofBytes 1) .Write output.global.protectedTags .VisitChildrenOfAccessed
    source selected maximum lower width sourceAfter childRuntime.formed.well childPositive.base.bounds outside writeContract.capacity
  have writtenFrame := GeneralBorrowFreshReadFrame.frame output.child.tree (.concrete output.tag)
    (Size.ofBytes offset) (Size.ofBytes 1) .Write output.global.protectedTags .VisitChildrenOfAccessed
  have nodes (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query = some node) :
      (output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes offset) (Size.ofBytes 1)
        .Write output.global.protectedTags .VisitChildrenOfAccessed).tree.nodeAt query = some node := by
    unfold BorrowTree.nodeAt
    rw [congrArg BorrowTree.nodes writtenFrame]
    exact oldNodes query node present
  have tags (oldTag : BorTag) (query : UniIndex) (present : tree.indexOfTag oldTag = some query) :
      (output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes offset) (Size.ofBytes 1)
        .Write output.global.protectedTags .VisitChildrenOfAccessed).tree.indexOfTag oldTag = some query := by
    unfold BorrowTree.indexOfTag
    rw [congrArg BorrowTree.tagMapping writtenFrame]
    exact oldTags oldTag query present
  have finalCapacity := writeContract.capacity.trans capacity
  have result := And.intro writeContract.completed (And.intro sourceWritten (And.intro writeRuntime
    (And.intro finalCapacity (And.intro nodes tags))))
  have shape := actual
  simp only [GeneralBorrowRawWildcardFnEntryRuntime.operation,TypedRetagEmpty.allocate_tag global fresh,
    Except.bind,Except.pure,bind,pure] at shape
  have outputEq := Except.ok.inj shape
  subst output
  exact result
end DuplicatePrefix.S02WildcardReturnSameSource
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S02WildcardReturnSameSource." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved same-allocation wildcard source retention dependency {dependency}"
