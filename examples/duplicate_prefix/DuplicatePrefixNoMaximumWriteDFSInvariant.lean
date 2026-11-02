import duplicate_prefix.DuplicatePrefixResidualScopedWriteDFSInvariant
import duplicate_prefix.DuplicatePrefixNoMaximumWriteSnapshot
namespace DuplicatePrefix.DuplicatePrefixNoMaximumWriteDFSInvariant
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open GeneralBorrowWildcardVirtualLeaf (effective)
open GeneralBorrowWildcardSubtreeData (Weights)
open GeneralBorrowWildcardSubtreeStack GeneralBorrowProjection DuplicatePrefixResidualWriteWitnessPlan
open DuplicatePrefixResidualWriteDFSInvariant (seen)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
abbrev LoopState := DuplicatePrefixResidualScopedWriteDFSInvariant.LoopState
structure Invariant {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : Plan tree initial protections root rootPosition maximum) (state : LoopState) : Prop
    extends DuplicatePrefixResidualScopedWriteDFSInvariant.Invariant weights support plan state where
  snapshot : Snapshot tree state.1 protections root rootPosition maximum .Write support.contains

theorem initial {tree : BorrowTree} {location : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : Plan tree location protections root rootPosition maximum)
    (snapshot : Snapshot tree location protections root rootPosition maximum .Write support.contains)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections) :
    Invariant (initial := location) (protections := protections) (rootPosition := rootPosition) (maximum := maximum)
      weights support plan (location,false,.Completed,#[(root,false)],0) := by
  exact ⟨DuplicatePrefixResidualScopedWriteDFSInvariant.initial weights support plan coherent,snapshot⟩

theorem top_unvisited {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : Plan tree initial protections root rootPosition maximum)
    (location : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (post : Bool) (steps : Nat)
    (valid : Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum)
      weights support plan (location,witness,.Completed,stack.push (index,post),steps))
    (present : tree.nodes.get index = some node) : location.perms.get index = initial.perms.get index := by
  exact DuplicatePrefixResidualScopedWriteDFSInvariant.top_unvisited weights support plan location witness stack index node post steps valid.toInvariant present

theorem pop {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : Plan tree initial protections root rootPosition maximum)
    (location : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum)
      weights support plan (location,witness,.Completed,stack.push (index,false),steps))
    (present : tree.nodes.get index = some node)
    (skipped : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Write
      (relation location root index node maximum .Write rootPosition) = true) :
    Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum) weights support plan (location,witness,.Completed,stack,steps+1) := by
  exact ⟨DuplicatePrefixResidualScopedWriteDFSInvariant.pop weights support plan location witness stack index node steps valid.toInvariant present skipped,valid.snapshot⟩

theorem expand {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : Plan tree initial protections root rootPosition maximum)
    (authorization : Authorization tree initial protections root rootPosition maximum .Write support.contains)
    (initialCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536) (scope : rootPosition ≠ 0 ∨ maximum = none)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (location : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum) weights support plan (location,witness,.Completed,stack.push (index,false),steps))
    (present : tree.nodes.get index = some node)
    (recurse : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Write
      (relation location root index node maximum .Write rootPosition) = false) :
    Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum) weights support plan (location,witness,.Completed,expanded stack index node.children,steps+1) := by
  exact ⟨DuplicatePrefixResidualScopedWriteDFSInvariant.expand weights support plan authorization initialCoherent short scope forest location witness stack index node steps valid.toInvariant present recurse,valid.snapshot⟩

theorem post {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : Plan tree initial protections root rootPosition maximum)
    (location after : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum)
      weights support plan (location,witness,.Completed,stack.push (index,true),steps))
    (present : tree.nodes.get index = some node)
    (removed : List UniIndex) (legal : Removal tree initial protections maximum .Write removed)
    (matching : Matches tree initial after protections .Write removed)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree after protections)
    (snapshot : Snapshot tree after protections root rootPosition maximum .Write support.contains)
    (other : ∀ query, query ≠ index → after.perms.get query = location.perms.get query) :
    Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum) weights support plan (after,seen location index node maximum protections witness,.Completed,stack,steps+1) := by
  exact ⟨DuplicatePrefixResidualScopedWriteDFSInvariant.post weights support plan location after witness stack index node steps valid.toInvariant present removed legal matching coherent other,snapshot⟩
end DuplicatePrefix.DuplicatePrefixNoMaximumWriteDFSInvariant
