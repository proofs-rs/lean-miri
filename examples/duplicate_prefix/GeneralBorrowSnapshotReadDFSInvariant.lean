import duplicate_prefix.GeneralBorrowSnapshotReadDFSPlan
namespace DuplicatePrefix.GeneralBorrowSnapshotReadDFSInvariant
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization
open GeneralBorrowWildcardVirtualLeaf (effective)
open GeneralBorrowExposedNonleafState (ReadFrame)
open GeneralBorrowWildcardSubtreeData (Weights)
open GeneralBorrowWildcardSubtreeStack
open GeneralBorrowWildcardPrimaryReadWitness (PointwiseReadFrame)
open GeneralBorrowSnapshotReadDFSPlan
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

abbrev LoopState := LocationTree × Bool × BorrowTree.WildcardAccessStatus × Array Task × Nat

def PendingSkip (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (rootPosition : Nat) (maximum : Option BorTag) (stack : Array Task) : Prop :=
  ∀ index node, (index,true) ∈ stack.toList → tree.nodes.get index = some node →
    DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Read
      (relation location root index node maximum .Read rootPosition) = false

structure Invariant {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : WitnessPlan tree initial protections root rootPosition maximum) (state : LoopState) : Prop where
  status : state.2.2.1 = .Completed
  snapshot : Snapshot tree state.1 protections root rootPosition maximum .Read support.contains
  frame : ReadFrame initial state.1
  pointwise : PointwiseReadFrame tree protections initial state.1
  coherent : GeneralBorrowExposureCardinality.LocationCoherent tree state.1 protections
  pending : PendingSkip tree state.1 root rootPosition maximum state.2.2.2.1
  control : GeneralBorrowWildcardControlStack.Invariant weights support state.2.2.2.1 state.2.2.2.2
  witness : plan.pending state.2.1 state.2.2.2.1
  outside : ∀ query, ¬support.contains query → state.1.perms.get query = initial.perms.get query

theorem initial {tree : BorrowTree} {location : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : WitnessPlan tree location protections root rootPosition maximum)
    (snapshot : Snapshot tree location protections root rootPosition maximum .Read support.contains)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections) :
    Invariant weights support plan (location,false,.Completed,#[(root,false)],0) := by
  refine ⟨rfl,snapshot,(fun _ => rfl),(fun _ _ _ => rfl),coherent,?_,
    GeneralBorrowWildcardControlStack.initial weights support,plan.initial,(fun _ _ => rfl)⟩
  intro index node member present
  simp at member

theorem pop {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : WitnessPlan tree initial protections root rootPosition maximum)
    (location : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : Invariant weights support plan (location,witness,.Completed,stack.push (index,false),steps))
    (present : tree.nodes.get index = some node)
    (skipped : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Read
      (relation location root index node maximum .Read rootPosition) = true) :
    Invariant weights support plan (location,witness,.Completed,stack,steps+1) := by
  refine ⟨rfl,valid.snapshot,valid.frame,valid.pointwise,valid.coherent,?_,
    GeneralBorrowWildcardControlStack.pop weights support stack (index,false) steps valid.control,
    plan.pop location witness stack index node present valid.frame valid.witness skipped,valid.outside⟩
  intro query queryNode member found
  exact valid.pending query queryNode (by simp [member]) found

theorem expand {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : WitnessPlan tree initial protections root rootPosition maximum)
    (location : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : Invariant weights support plan (location,witness,.Completed,stack.push (index,false),steps))
    (present : tree.nodes.get index = some node)
    (recurse : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Read
      (relation location root index node maximum .Read rootPosition) = false) :
    Invariant weights support plan (location,witness,.Completed,expanded stack index node.children,steps+1) := by
  refine ⟨rfl,valid.snapshot,valid.frame,valid.pointwise,valid.coherent,?_,
    GeneralBorrowWildcardControlStack.expand weights support stack index node steps valid.control present,
    plan.expand witness stack index node present valid.witness,valid.outside⟩
  intro query queryNode member found
  simp only [expanded,Array.toList_append,Array.toList_push,Array.toList_map,List.mem_append] at member
  rcases member with old | child
  · rcases old with earlier | current
    · exact valid.pending query queryNode (by simp [earlier]) found
    · have same : query = index := by simpa using current
      subst query
      have nodeEq := Option.some.inj (present.symm.trans found)
      subst queryNode
      exact recurse
  · obtain ⟨child,childMember,impossible⟩ := List.mem_map.mp child
    simp at impossible

theorem post {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : WitnessPlan tree initial protections root rootPosition maximum)
    (location after : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : Invariant weights support plan (location,witness,.Completed,stack.push (index,true),steps))
    (present : tree.nodes.get index = some node)
    (snapshot : Snapshot tree after protections root rootPosition maximum .Read support.contains)
    (frame : ReadFrame location after)
    (pointwise : PointwiseReadFrame tree protections location after)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree after protections)
    (other : ∀ query, query ≠ index → after.perms.get query = location.perms.get query) :
    Invariant weights support plan
      (after,seen location index node maximum protections witness,.Completed,stack,steps+1) := by
  refine ⟨rfl,snapshot,(fun query => (frame query).trans (valid.frame query)),
    (fun query queryNode found => (pointwise query queryNode found).trans (valid.pointwise query queryNode found)),
    coherent,?_,GeneralBorrowWildcardControlStack.pop weights support stack (index,true) steps valid.control,
    plan.post location witness stack index node present valid.pointwise valid.witness,?_⟩
  · intro query queryNode member found
    have different := GeneralBorrowWildcardControlStack.pending_different weights support stack index true steps valid.control query member
    rw [GeneralBorrowSnapshotReadState.relation_frame location after frame]
    change DuplicatePrefixCallbackVisitAuthorization.entrySkip
      (((after.perms.get query).getD queryNode.defaultLocationState)) .Read _ = false
    rw [other query different]
    exact valid.pending query queryNode (by simp [member]) found
  · intro query outside
    have included := valid.control.known (index,true) (by simp)
    have different : query ≠ index := by intro same; subst query; exact outside included
    exact (other query different).trans (valid.outside query outside)

end DuplicatePrefix.GeneralBorrowSnapshotReadDFSInvariant
