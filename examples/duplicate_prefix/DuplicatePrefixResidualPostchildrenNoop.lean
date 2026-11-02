import duplicate_prefix.DuplicatePrefixCallbackVisitAuthorizationRepaired
import duplicate_prefix.GeneralBorrowResidualSavedWriteRuntime

/-! One missing postvisit case, without changing the legacy authorization or
DFS theorems. PendingSaved remembers an ENTRY mask with skip=false; it does
not require the CURRENT exit query to recurse. RuntimeInvariant has no old
Authorization/queries field. Support.of_authorization is optional, and virtual
witness plans are independent of authorization. The legacy expand proof does
consume old Authorization; this module neither reuses that proof for the new
domain nor claims a complete revised traversal theorem. -/
namespace DuplicatePrefix.DuplicatePrefixResidualPostchildrenNoop
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
open DuplicatePrefixResidualCountModel DuplicatePrefixResidualSavedWriteDFSInvariant
open DuplicatePrefixResidualWriteWitnessPlan GeneralBorrowResidualSavedWriteRuntime
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
open GeneralBorrowWildcardSubtreeData (Weights)
open GeneralBorrowWildcardSubtreeStack
open GeneralBorrowSnapshotReadRuntime (GlobalPossible)
open DuplicatePrefixResidualWriteDFSInvariant (seen)
open DuplicatePrefixCallbackVisitAuthorizationRepaired
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Storage materialization changes no present node's effective state. All
child updates and the CURRENT cache survive; the removal mask is unchanged.
These are internal algebraic/runtime facts, not a caller safety premise. -/
theorem materialized_preserves (tree : BorrowTree) (initial current : LocationTree)
    (protections : ProtectedTags) (maximum : Option BorTag) (removed : List UniIndex)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (legal : Removal tree initial protections maximum .Write removed)
    (matching : Matches tree initial current protections .Write removed)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree current protections)
    (possible : GlobalPossible tree current) :
    Removal tree initial protections maximum .Write removed ∧
    Matches tree initial (materialized current index node) protections .Write removed ∧
    (materialized current index node).exposedCache = current.exposedCache ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree (materialized current index node) protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree (materialized current index node) protections ∧
    GlobalPossible tree (materialized current index node) ∧
    (∀ query, query ≠ index → (materialized current index node).perms.get query = current.perms.get query) ∧
    (∀ query, tree.nodes.get query = none → (materialized current index node).perms.get query = current.perms.get query) := by
  have other : ∀ query, query ≠ index → (materialized current index node).perms.get query = current.perms.get query := by
    intro query different
    unfold materialized UniValMap.orInsert
    split
    · rfl
    · exact GeneralBorrowFreshLocation.get_other _ index query _ different
  refine ⟨legal,?_,rfl,GeneralBorrowExposedNonleafCoherence.materialized_coherent tree current index node protections present coherent,
    GeneralBorrowSnapshotReadRuntime.materialized_profile tree current protections index node present profile,
    ?_,other,GeneralBorrowSnapshotReadRuntime.vacant_frame tree current _ index node present other⟩
  · intro query queryNode found exposed
    change GeneralBorrowExposureCardinality.supports
      ((effective (materialized current index node) query queryNode).permission.strongestAllowedLocalAccess
        (protections.contains queryNode.tag)) .Write = _
    rw [GeneralBorrowExposedVirtualSchedule.materialized_effective tree current index node present query queryNode found]
    exact matching query queryNode found exposed
  · intro query queryNode found
    rw [GeneralBorrowExposedVirtualSchedule.materialized_effective tree current index node present query queryNode found]
    exact possible query queryNode found

/-- The EXISTING auth-free post invariant accepts the additional materialized
outcome. No old Action (whose exact branch requires recordNewAccess) is used. -/
theorem preserve_runtime {tree : BorrowTree} {initial current : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {position : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : Plan tree initial protections root position maximum) (witness : Bool)
    (stack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : RuntimeInvariant (initial := initial) (protections := protections)
      (rootPosition := position) (maximum := maximum) weights support plan
      (current,witness,.Completed,stack.push (index,true),steps))
    (present : tree.nodes.get index = some node) :
    RuntimeInvariant (initial := initial) (protections := protections)
      (rootPosition := position) (maximum := maximum) weights support plan
      (materialized current index node,seen current index node maximum protections witness,.Completed,stack,steps+1) := by
  obtain ⟨base,profile,possible,vacant⟩ := valid
  obtain ⟨removed,legal,matching,pending⟩ := base.model
  obtain ⟨legal,matching,cache,coherent,profile,possible,other,frame⟩ :=
    materialized_preserves tree initial current protections maximum removed index node present legal matching base.coherent profile possible
  refine ⟨DuplicatePrefixResidualSavedWriteDFSInvariant.post weights support plan current _ witness stack index node steps
    base present removed removed pending (fun _ member => member) legal matching coherent other,profile,possible,?_⟩
  intro query missing
  exact (frame query missing).trans (vacant query missing)

/-- The witness is observed BEFORE materialization, just as in the core. -/
theorem seen_source (current : LocationTree) (index : UniIndex) (node : TreeNode)
    (maximum : Option BorTag) (protections : ProtectedTags) (witness : Bool) :
    seen current index node maximum protections witness = (witness ||
      (node.isExposed && ((effective current index node).permission.strongestAllowedLocalAccess
        (protections.contains node.tag)).allows .Write &&
        (maximum.isNone || maximum.any (fun tag => tag.value >= node.tag.value)))) := by
  unfold seen
  split <;> simp_all

/-- Actual source-loop consumption plus preservation, for an arbitrary current
location/pending stack. The guard is transparent data on the recomputed EXIT
query; no callback success, old authorization, Row or future Result is assumed. -/
theorem post_noop {tree : BorrowTree} {initial current : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {position : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (rootBound : weights.weight root ≤ tree.nodes.size)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : Plan tree initial protections root position maximum) (witness : Bool)
    (stack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : RuntimeInvariant (initial := initial) (protections := protections)
      (rootPosition := position) (maximum := maximum) weights support plan
      (current,witness,.Completed,stack.push (index,true),steps))
    (present : tree.nodes.get index = some node)
    (guard : PostchildrenNoop (effective current index node) .Write (protections.contains node.tag)
      (relation current root index node maximum .Write position)) :
    ∃ scan : Unit → LoopState → Id (ForInStep LoopState),
      (tree.performWildcardAccessAt initial root maximum .Write protections (position != 0) =
        let final := Lean.Loop.forIn {} (initial,false,.Completed,#[(root,false)],0) scan
        ⟨final.1,if final.2.2.1 == .Completed && !final.2.1 && !(position != 0) then
          .NoValidExposedReferences root none else final.2.2.1⟩) ∧
      scan () (current,witness,.Completed,stack.push (index,true),steps) =
        .yield (materialized current index node,seen current index node maximum protections witness,.Completed,stack,steps+1) ∧
      RuntimeInvariant (initial := initial) (protections := protections)
        (rootPosition := position) (maximum := maximum) weights support plan
        (materialized current index node,seen current index node maximum protections witness,.Completed,stack,steps+1) := by
  obtain ⟨scan,identity,post⟩ := actual_postchildren tree initial root maximum .Write protections (position != 0)
  refine ⟨scan,identity,?_,preserve_runtime weights support plan witness stack index node steps valid present⟩
  have budget := GeneralBorrowWildcardControlStack.not_past weights support _ steps valid.1.control rootBound
  have related := (relation_source current root index node maximum .Write position).symm.trans guard.1
  have scalar : PostchildrenNoop (effective current index node) .Write (protections.contains node.tag) (some .ForeignAccess) := by
    simpa only [guard.1] using guard
  have step := post current index node stack steps witness present budget
    (by cases maximum <;> simpa only [aboveMaximum] using related) scalar
  rw [seen_source current index node maximum protections witness]
  exact step

end DuplicatePrefix.DuplicatePrefixResidualPostchildrenNoop
