import duplicate_prefix.DuplicatePrefixResidualSavedWriteDFSInvariant
import duplicate_prefix.DuplicatePrefixPrimaryWriteClosureState
import duplicate_prefix.DuplicatePrefixResidualWriteWitnessPlan
import duplicate_prefix.DuplicatePrefixResidualSavedWritePost
import duplicate_prefix.DuplicatePrefixResidualWritePost
import duplicate_prefix.DuplicatePrefixResidualWriteSkip
import duplicate_prefix.GeneralBorrowWildcardUntouched
namespace DuplicatePrefix.DuplicatePrefixPrimaryWriteThinInvariant
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open GeneralBorrowWildcardVirtualLeaf (effective)
open GeneralBorrowWildcardSubtreeData (Weights)
open GeneralBorrowWildcardSubtreeStack
open GeneralBorrowProjection
open DuplicatePrefixPrimaryWriteClosureModel
open DuplicatePrefixPrimaryWriteClosureState (Safe)
open DuplicatePrefixResidualWriteWitnessPlan
open DuplicatePrefixResidualWriteDFSInvariant (seen)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
abbrev LoopState := LocationTree × Bool × BorrowTree.WildcardAccessStatus × Array Task × Nat

def PendingSaved (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags) (root : UniIndex)
    (maximum : Option BorTag) (stack : Array Task) (removed : List UniIndex) : Prop :=
  ∀ index node, (index,true) ∈ stack.toList → tree.nodes.get index = some node →
    ∃ before, Removal tree initial protections maximum .Write before ∧ (∀ query ∈ before, query ∈ removed) ∧
      DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective initial index node) .Write
        (residualRelation tree initial protections root index node maximum .Write 0 before) = false

structure Invariant {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : Plan tree initial protections root 0 maximum) (state : LoopState) : Prop where
  status : state.2.2.1 = .Completed
  model : ∃ removed, Removal tree initial protections maximum .Write removed ∧
    Matches tree initial state.1 protections .Write removed ∧
    PendingSaved tree initial protections root maximum state.2.2.2.1 removed ∧
    CutoffOrigin tree initial state.1 protections maximum ∧
    Safe tree initial state.1 protections root maximum removed support.contains
  coherent : GeneralBorrowExposureCardinality.LocationCoherent tree state.1 protections
  control : GeneralBorrowWildcardControlStack.Invariant weights support state.2.2.2.1 state.2.2.2.2
  disjoint : GeneralBorrowWildcardTaskRegions.Disjoint (source_normal_projection tree initial protections).topology state.2.2.2.1
  untouched : GeneralBorrowWildcardUntouched.Untouched (source_normal_projection tree initial protections).topology initial state.1 state.2.2.2.1
  outside : ∀ query, ¬support.contains query → state.1.perms.get query = initial.perms.get query
  witness : plan.pending state.2.1 state.2.2.2.1

/-- Forget only the primary closure data to recover the existing saved DFS invariant. -/
theorem Invariant.to_saved {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {maximum : Option BorTag}
    {weights : Weights tree} {support : GeneralBorrowWildcardControlStack.Support tree root}
    {plan : Plan tree initial protections root 0 maximum} {state : LoopState}
    (valid : Invariant weights support plan state) :
    DuplicatePrefixResidualSavedWriteDFSInvariant.Invariant (initial := initial) (protections := protections)
      (rootPosition := 0) (maximum := maximum) weights support plan state := by
  refine ⟨valid.status,?_,valid.coherent,valid.control,valid.disjoint,valid.untouched,valid.outside,valid.witness⟩
  obtain ⟨removed,legal,matching,pending,origin,safe⟩ := valid.model
  exact ⟨removed,legal,matching,pending⟩

theorem Invariant.basic {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {maximum : Option BorTag}
    {weights : Weights tree} {support : GeneralBorrowWildcardControlStack.Support tree root}
    {plan : Plan tree initial protections root 0 maximum} {state : LoopState}
    (valid : Invariant weights support plan state) : Model tree initial state.1 protections maximum := by
  obtain ⟨removed,legal,matching,pending,origin,safe⟩ := valid.model
  exact ⟨removed,legal,matching⟩

theorem initial {tree : BorrowTree} {location : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : Plan tree location protections root 0 maximum)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections) :
    Invariant (initial := location) (protections := protections) (maximum := maximum)
      weights support plan (location,false,.Completed,#[(root,false)],0) := by
  refine ⟨rfl,⟨[],empty_removal tree location protections maximum .Write,?_,?_,
      (by intro index node present exposed above supported; rfl),
      DuplicatePrefixPrimaryWriteClosureState.safe_initial tree location protections root maximum support.contains⟩,coherent,
    GeneralBorrowWildcardControlStack.initial weights support,
    GeneralBorrowWildcardTaskRegions.initial _ root,GeneralBorrowWildcardUntouched.initial _ location root,?_,plan.initial⟩
  · intro index node present exposed
    simp [levels]
  · intro index node member present
    simp at member
  · intro query outside
    rfl

theorem top_unvisited {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : Plan tree initial protections root 0 maximum)
    (location : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (post : Bool) (steps : Nat)
    (valid : Invariant (initial := initial) (protections := protections) (maximum := maximum)
      weights support plan (location,witness,.Completed,stack.push (index,post),steps))
    (present : tree.nodes.get index = some node) : location.perms.get index = initial.perms.get index := by
  have bounded := GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node present
  have projected : index.toNat < (source_normal_projection tree initial protections).topology.nodes.size := by
    unfold_general_projection
    unfold_general_topology
    simpa only [Array.size_map] using bounded
  exact GeneralBorrowWildcardUntouched.top _ initial location stack index post projected valid.untouched

theorem pop {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : Plan tree initial protections root 0 maximum)
    (location : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : Invariant (initial := initial) (protections := protections) (maximum := maximum)
      weights support plan (location,witness,.Completed,stack.push (index,false),steps))
    (present : tree.nodes.get index = some node)
    (skipped : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Write
      (relation location root index node maximum .Write 0) = true) :
    Invariant (initial := initial) (protections := protections) (maximum := maximum) weights support plan (location,witness,.Completed,stack,steps+1) := by
  obtain ⟨removed,legal,matching,pending,origin,safe⟩ := valid.model
  refine ⟨rfl,⟨removed,legal,matching,?_,origin,safe⟩,valid.coherent,GeneralBorrowWildcardControlStack.pop weights support stack (index,false) steps valid.control,
    GeneralBorrowWildcardTaskRegions.pop _ stack (index,false) valid.disjoint,
    GeneralBorrowWildcardUntouched.pop _ initial location stack (index,false) valid.untouched,valid.outside,plan.pop location witness stack index node present valid.basic valid.coherent valid.witness skipped⟩
  intro query node member present
  exact pending query node (by simp [member]) present

theorem expand {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : Plan tree initial protections root 0 maximum)
    (authorization : Authorization tree initial protections root 0 maximum .Write support.contains)
    (initialCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (location : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : Invariant (initial := initial) (protections := protections) (maximum := maximum) weights support plan (location,witness,.Completed,stack.push (index,false),steps))
    (present : tree.nodes.get index = some node)
    (recurse : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Write
      (relation location root index node maximum .Write 0) = false) :
    Invariant (initial := initial) (protections := protections) (maximum := maximum) weights support plan (location,witness,.Completed,expanded stack index node.children,steps+1) := by
  have unvisited := top_unvisited weights support plan location witness stack index node false steps valid present
  obtain ⟨removed,legal,matching,pending,origin,safe⟩ := valid.model
  have savedActive : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective initial index node) .Write
      (residualRelation tree initial protections root index node maximum .Write 0 removed) = false := by
    rw [←relation_matches tree initial location protections .Write removed matching valid.coherent short root index node maximum 0]
    simpa only [effective,unvisited] using recurse
  obtain ⟨disjoint,untouched⟩ := GeneralBorrowWildcardUntouched.expand_actual tree initial protections forest initial location stack index node present valid.disjoint valid.untouched
  refine ⟨rfl,⟨removed,legal,matching,?_,origin,safe⟩,valid.coherent,GeneralBorrowWildcardControlStack.expand weights support stack index node steps valid.control present,
    disjoint,untouched,valid.outside,plan.expand witness stack index node present valid.witness⟩
  intro query queryNode member found
  simp only [expanded,Array.toList_append,Array.toList_push,Array.toList_map,List.mem_append] at member
  rcases member with old | child
  · rcases old with earlier | current
    · exact pending query queryNode (by simp [earlier]) found
    · have same : query = index := by simpa using current
      subst query
      have nodeEq := Option.some.inj (present.symm.trans found)
      subst queryNode
      exact ⟨removed,legal,(by intro query member;exact member),savedActive⟩
  · obtain ⟨child,childMember,impossible⟩ := List.mem_map.mp child
    simp at impossible

theorem post {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : Plan tree initial protections root 0 maximum)
    (location after : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : Invariant (initial := initial) (protections := protections) (maximum := maximum)
      weights support plan (location,witness,.Completed,stack.push (index,true),steps))
    (present : tree.nodes.get index = some node)
    (removed afterRemoved : List UniIndex)
    (pending : PendingSaved tree initial protections root maximum (stack.push (index,true)) removed)
    (subset : ∀ query ∈ removed, query ∈ afterRemoved)
    (legal : Removal tree initial protections maximum .Write afterRemoved)
    (matching : Matches tree initial after protections .Write afterRemoved)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree after protections)
    (other : ∀ query, query ≠ index → after.perms.get query = location.perms.get query)
    (origin : CutoffOrigin tree initial after protections maximum)
    (safe : Safe tree initial after protections root maximum afterRemoved support.contains) :
    Invariant (initial := initial) (protections := protections) (maximum := maximum) weights support plan (after,seen location index node maximum protections witness,.Completed,stack,steps+1) := by
  refine ⟨rfl,⟨afterRemoved,legal,matching,?_,origin,safe⟩,coherent,GeneralBorrowWildcardControlStack.pop weights support stack (index,true) steps valid.control,
    GeneralBorrowWildcardTaskRegions.pop _ stack (index,true) valid.disjoint,
    GeneralBorrowWildcardUntouched.post _ initial location after stack index valid.disjoint valid.untouched other,?_,plan.post location witness stack index node present valid.basic valid.witness⟩
  · intro query queryNode member found
    obtain ⟨before,legalBefore,included,active⟩ := pending query queryNode (by simp [member]) found
    exact ⟨before,legalBefore,(by intro next inside;exact subset next (included next inside)),active⟩
  · intro query outside
    have different : query ≠ index := by
      intro same
      subst query
      exact outside (valid.control.known (index,true) (by simp))
    exact (other query different).trans (valid.outside query outside)
end DuplicatePrefix.DuplicatePrefixPrimaryWriteThinInvariant
