import duplicate_prefix.DuplicatePrefixResidualWriteDFSInvariant
import duplicate_prefix.DuplicatePrefixVirtualWriteClosureState
namespace DuplicatePrefix.DuplicatePrefixVirtualWriteClosureInvariant
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open GeneralBorrowWildcardVirtualLeaf (effective)
open GeneralBorrowWildcardSubtreeData (Weights)
open GeneralBorrowWildcardSubtreeStack
open GeneralBorrowProjection
open DuplicatePrefixResidualReadWriteEffects (Origin)
open DuplicatePrefixVirtualWriteClosureState (Safe)
open DuplicatePrefixResidualWriteDFSInvariant (seen)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
abbrev LoopState := DuplicatePrefixResidualWriteDFSInvariant.LoopState
structure Invariant {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root) (state : LoopState) : Prop
    extends toBase : DuplicatePrefixResidualWriteDFSInvariant.Invariant (initial := initial) (protections := protections)
      (rootPosition := rootPosition) (maximum := maximum) weights support state where
  closure : ∃ removed, Removal tree initial protections maximum .Write removed ∧
    Matches tree initial state.1 protections .Write removed ∧ Origin tree initial state.1 protections ∧
    Safe tree initial state.1 protections root rootPosition maximum removed support.contains

theorem initial {tree : BorrowTree} {location : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections) :
    Invariant (initial := location) (protections := protections) (rootPosition := rootPosition) (maximum := maximum)
      weights support (location,false,.Completed,#[(root,false)],0) := by
  refine ⟨DuplicatePrefixResidualWriteDFSInvariant.initial weights support coherent,[],empty_removal tree location protections maximum .Write,?_,
    DuplicatePrefixResidualReadWriteEffects.origin_initial tree location protections,
    DuplicatePrefixVirtualWriteClosureState.safe_initial tree location protections root rootPosition maximum support.contains⟩
  intro index node present exposed
  simp [levels]

theorem top_unvisited {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (location : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (post : Bool) (steps : Nat)
    (valid : Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum)
      weights support (location,witness,.Completed,stack.push (index,post),steps))
    (present : tree.nodes.get index = some node) : location.perms.get index = initial.perms.get index := by
  exact DuplicatePrefixResidualWriteDFSInvariant.top_unvisited weights support location witness stack index node post steps valid.toBase present

theorem pop {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (location : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (steps : Nat)
    (valid : Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum)
      weights support (location,witness,.Completed,stack.push (index,false),steps)) :
    Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum) weights support (location,witness,.Completed,stack,steps+1) := by
  exact ⟨DuplicatePrefixResidualWriteDFSInvariant.pop weights support location witness stack index steps valid.toBase,valid.closure⟩

theorem expand {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (authorization : Authorization tree initial protections root rootPosition maximum .Write support.contains)
    (initialCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536) (virtual : rootPosition ≠ 0)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (location : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum) weights support (location,witness,.Completed,stack.push (index,false),steps))
    (present : tree.nodes.get index = some node)
    (recurse : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Write
      (relation location root index node maximum .Write rootPosition) = false) :
    Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum) weights support (location,witness,.Completed,expanded stack index node.children,steps+1) := by
  exact ⟨DuplicatePrefixResidualWriteDFSInvariant.expand weights support authorization initialCoherent short virtual forest location witness stack index node steps valid.toBase present recurse,valid.closure⟩

theorem post {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (location after : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum)
      weights support (location,witness,.Completed,stack.push (index,true),steps))
    (removed : List UniIndex) (legal : Removal tree initial protections maximum .Write removed)
    (matching : Matches tree initial after protections .Write removed)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree after protections)
    (other : ∀ query, query ≠ index → after.perms.get query = location.perms.get query)
    (origin : Origin tree initial after protections)
    (safe : Safe tree initial after protections root rootPosition maximum removed support.contains) :
    Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum) weights support (after,seen location index node maximum protections witness,.Completed,stack,steps+1) := by
  exact ⟨DuplicatePrefixResidualWriteDFSInvariant.post weights support location after witness stack index node steps valid.toBase removed legal matching coherent other,
    removed,legal,matching,origin,safe⟩
end DuplicatePrefix.DuplicatePrefixVirtualWriteClosureInvariant
