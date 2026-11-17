import duplicate_prefix.DuplicatePrefixResidualWritePost
import duplicate_prefix.DuplicatePrefixResidualWriteSkip
import duplicate_prefix.GeneralBorrowWildcardUntouched
namespace DuplicatePrefix.DuplicatePrefixResidualWriteDFSInvariant
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open GeneralBorrowWildcardVirtualLeaf (effective)
open GeneralBorrowWildcardSubtreeData (Weights)
open GeneralBorrowWildcardSubtreeStack
open GeneralBorrowProjection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
abbrev LoopState := LocationTree × Bool × BorrowTree.WildcardAccessStatus × Array Task × Nat

def seen (location : LocationTree) (index : UniIndex) (node : TreeNode)
    (maximum : Option BorTag) (protections : ProtectedTags) (witness : Bool) : Bool :=
  if node.isExposed &&
      ((effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows .Write &&
      (maximum.isNone || maximum.any (fun tag => tag.value >= node.tag.value)) then true else witness

def PendingSkip (tree : BorrowTree) (initial : LocationTree) (root : UniIndex)
    (rootPosition : Nat) (maximum : Option BorTag) (stack : Array Task) : Prop :=
  ∀ index node, (index,true) ∈ stack.toList → tree.nodes.get index = some node →
    DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective initial index node) .Write
      (relation initial root index node maximum .Write rootPosition) = false

structure Invariant {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root) (state : LoopState) : Prop where
  status : state.2.2.1 = .Completed
  model : ∃ removed, Removal tree initial protections maximum .Write removed ∧
    Matches tree initial state.1 protections .Write removed
  coherent : GeneralBorrowExposureCardinality.LocationCoherent tree state.1 protections
  pending : PendingSkip tree initial root rootPosition maximum state.2.2.2.1
  control : GeneralBorrowWildcardControlStack.Invariant weights support state.2.2.2.1 state.2.2.2.2
  disjoint : GeneralBorrowWildcardTaskRegions.Disjoint (source_normal_projection tree initial protections).topology state.2.2.2.1
  untouched : GeneralBorrowWildcardUntouched.Untouched (source_normal_projection tree initial protections).topology initial state.1 state.2.2.2.1
  outside : ∀ query, ¬support.contains query → state.1.perms.get query = initial.perms.get query

theorem initial {tree : BorrowTree} {location : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections) :
    Invariant (initial := location) (protections := protections) (rootPosition := rootPosition) (maximum := maximum)
      weights support (location,false,.Completed,#[(root,false)],0) := by
  refine ⟨rfl,⟨[],empty_removal tree location protections maximum .Write,?_⟩,coherent,?_,
    GeneralBorrowWildcardControlStack.initial weights support,
    GeneralBorrowWildcardTaskRegions.initial _ root,GeneralBorrowWildcardUntouched.initial _ location root,?_⟩
  · intro index node present exposed
    simp [levels]
  · intro index node member present
    simp at member
  · intro query outside
    rfl

theorem top_unvisited {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (location : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (post : Bool) (steps : Nat)
    (valid : Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum)
      weights support (location,witness,.Completed,stack.push (index,post),steps))
    (present : tree.nodes.get index = some node) : location.perms.get index = initial.perms.get index := by
  have bounded := GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node present
  have projected : index.toNat < (source_normal_projection tree initial protections).topology.nodes.size := by
    unfold_general_projection
    unfold_general_topology
    simpa only [Array.size_map] using bounded
  exact GeneralBorrowWildcardUntouched.top _ initial location stack index post projected valid.untouched

theorem pop {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (location : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (steps : Nat)
    (valid : Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum)
      weights support (location,witness,.Completed,stack.push (index,false),steps)) :
    Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum) weights support (location,witness,.Completed,stack,steps+1) := by
  refine ⟨rfl,valid.model,valid.coherent,?_,GeneralBorrowWildcardControlStack.pop weights support stack (index,false) steps valid.control,
    GeneralBorrowWildcardTaskRegions.pop _ stack (index,false) valid.disjoint,
    GeneralBorrowWildcardUntouched.pop _ initial location stack (index,false) valid.untouched,valid.outside⟩
  intro query node member present
  exact valid.pending query node (by simp [member]) present

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
  have unvisited := top_unvisited weights support location witness stack index node false steps valid present
  obtain ⟨removed,legal,matching⟩ := valid.model
  have initialActive := DuplicatePrefixResidualWriteSkip.initially_not_skipped tree initial location protections root index node maximum rootPosition support.contains
    authorization removed legal matching initialCoherent valid.coherent short (valid.control.known (index,false) (by simp)) unvisited (.inl virtual) recurse
  obtain ⟨disjoint,untouched⟩ := GeneralBorrowWildcardUntouched.expand_actual tree initial protections forest initial location stack index node present valid.disjoint valid.untouched
  refine ⟨rfl,valid.model,valid.coherent,?_,GeneralBorrowWildcardControlStack.expand weights support stack index node steps valid.control present,
    disjoint,untouched,valid.outside⟩
  intro query queryNode member found
  simp only [expanded,Array.toList_append,Array.toList_push,Array.toList_map,List.mem_append] at member
  rcases member with old | child
  · rcases old with earlier | current
    · exact valid.pending query queryNode (by simp [earlier]) found
    · have same : query = index := by simpa using current
      subst query
      have nodeEq := Option.some.inj (present.symm.trans found)
      subst queryNode
      exact initialActive
  · obtain ⟨child,childMember,impossible⟩ := List.mem_map.mp child
    simp at impossible

theorem post {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (location after : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum)
      weights support (location,witness,.Completed,stack.push (index,true),steps))
    (removed : List UniIndex) (legal : Removal tree initial protections maximum .Write removed)
    (matching : Matches tree initial after protections .Write removed)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree after protections)
    (other : ∀ query, query ≠ index → after.perms.get query = location.perms.get query) :
    Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum) weights support (after,seen location index node maximum protections witness,.Completed,stack,steps+1) := by
  refine ⟨rfl,⟨removed,legal,matching⟩,coherent,?_,GeneralBorrowWildcardControlStack.pop weights support stack (index,true) steps valid.control,
    GeneralBorrowWildcardTaskRegions.pop _ stack (index,true) valid.disjoint,
    GeneralBorrowWildcardUntouched.post _ initial location after stack index valid.disjoint valid.untouched other,?_⟩
  · intro query queryNode member found
    exact valid.pending query queryNode (by simp [member]) found
  · intro query outside
    have different : query ≠ index := by
      intro same
      subst query
      exact outside (valid.control.known (index,true) (by simp))
    exact (other query different).trans (valid.outside query outside)
end DuplicatePrefix.DuplicatePrefixResidualWriteDFSInvariant
