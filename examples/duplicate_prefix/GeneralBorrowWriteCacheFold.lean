import duplicate_prefix.GeneralBorrowFrozenWriteExposure
import duplicate_prefix.GeneralBorrowNormalEventCacheFrame
namespace DuplicatePrefix.GeneralBorrowWriteCacheFold
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowFrozenWriteExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- A projection of an actual dependent source loop to an exact cache fold. -/
theorem loop_fold {α : Type} (events : List α)
    (scan : (event : α) → event ∈ events → LocationTree × Except ExposedCacheError Unit → Id (ForInStep (LocationTree × Except ExposedCacheError Unit)))
    (delta : ExposedCache → α → ExposedCache)
    (step : ∀ event member location, ∃ nextLocation,
      scan event member (location,.ok ()) = .yield (nextLocation,.ok ()) ∧
      nextLocation.exposedCache = delta location.exposedCache event)
    (location : LocationTree) :
    (forIn' events (location,.ok ()) scan).1.exposedCache = events.foldl delta location.exposedCache ∧
    (forIn' events (location,.ok ()) scan).2 = .ok () := by
  induction events generalizing location with
  | nil => exact ⟨rfl,rfl⟩
  | cons event rest ih =>
    obtain ⟨next,actual,cache⟩ := step event (by simp) location
    simp only [List.forIn'_cons,actual,bind,List.foldl_cons]
    have later := ih (fun other member => scan other (by simp [member]))
      (fun other member current => step other (by simp [member]) current) next
    rw [cache] at later
    exact later

/-- Frozen foreign visitors decrement their own and the root's Read counters;
the root's Unique local visitor leaves the cache unchanged. -/
def delta (root : UniIndex) (cache : ExposedCache) (position : Nat) : ExposedCache :=
  match UniIndex.ofNat? position with
  | none => cache
  | some index => if index = root then cache else dropRead (dropRead cache index) root

set_option autoImplicit false in
/-- Raw transition metadata for one actual successful Write event. This
intermediate API requires no cache correctness or cache-success premise. -/
structure EventMetadata (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (mode : ChildrenVisitMode) (event : TraversalEvent) where
  index : UniIndex
  node : TreeNode
  oldState : LocationState
  newState : LocationState
  converted : UniIndex.ofNat? event.node = some index
  present : tree.nodeAt index = some node
  oldPresent : tree.locationStateAt location index = some oldState
  newPresent : ((source_normal_projection tree location {}).performAccess root.toNat .Write mode).tree.stateAt event.node = some newState
  exposed : node.isExposed = true
  transition : (index = root ∧ oldState.permission = .Unique ∧ event.relatedness = .LocalAccess) ∨
    (index ≠ root ∧ node.parent = some root ∧ oldState.permission = .Frozen ∧
      newState.permission = .Disabled ∧ event.relatedness = .ForeignAccess)
/-- Exact source normal Write cache loop, before cardinality aggregation.
Successful normal permissions are derived from forest/ownership, not assumed. -/
theorem normal (tree : BorrowTree) (location : LocationTree) (root : UniIndex) (rootNode : TreeNode)
    (mode : ChildrenVisitMode) (present : tree.nodeAt root = some rootNode) (parentless : rootNode.parent = none)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location {}).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location {}) root.toNat .Write)
    (metadata : ∀ event ∈ ((source_normal_projection tree location {}).performAccess root.toNat .Write mode).visited,
      Nonempty (EventMetadata tree location root mode event)) :
    (tree.performNormalAccessAt location root .Write {} mode).location.exposedCache =
      (((source_normal_projection tree location {}).performAccess root.toNat .Write mode).visited.map TraversalEvent.node).foldl
        (delta root) location.exposedCache ∧
    (tree.performNormalAccessAt location root .Write {} mode).outcome = .ok () := by
  have completed := GeneralBorrowTraversal.normal_access _ forest root.toNat .Write mode owned
  unfold BorrowTree.performNormalAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_normal_cache_scan
  have step : ∀ event member current, ∃ nextLocation,
      scan event member (current,.ok ()) = .yield (nextLocation,.ok ()) ∧
      nextLocation.exposedCache = delta root current.exposedCache event.node := by
    intro event member current
    obtain ⟨facts⟩ := metadata event member
    obtain ⟨index,node,oldState,newState,converted,nodePresent,oldPresent,newPresent,exposed,transition⟩ := facts
    rcases transition with ⟨same,permission,related⟩ | ⟨different,parent,oldPermission,newPermission,related⟩
    · refine ⟨current,?_,?_⟩
      · have noop : performAccessTransition .Write .LocalAccess .Unique (({} : ProtectedTags).contains node.tag) = .Transition ⟨.Unique,.Unique⟩ := by
          cases held : (({} : ProtectedTags).contains node.tag) <;> rfl
        simp only [scan,converted,nodePresent,oldPresent,newPresent,permission,related,noop,PermTransition.isNoop,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,ite_false,ite_self]
      · simp only [delta,converted,ite_eq_left same]
    · have update := two_nodes current.exposedCache tree.nodes index root node rootNode nodePresent present parent parentless
      refine ⟨{current with exposedCache := dropRead (dropRead current.exposedCache index) root},?_,?_⟩
      · simp only [scan,converted,nodePresent,exposed,completed,oldPresent,newPresent,
          oldPermission,newPermission,related,ProtectedTags.contains,ProtectedTags.get]
        erw [update]
        rfl
      · simp only [delta,converted,ite_eq_right different]
  have fold := loop_fold _ scan (fun cache event => delta root cache event.node) step
    (source_write_states location ((source_normal_projection tree location {}).performAccess root.toNat .Write mode).tree.locationStates)
  have initial := checked_materialized_cache location
    ((source_normal_projection tree location {}).performAccess root.toNat .Write mode).tree.locationStates
  rw [initial] at fold
  rw [List.foldl_map]
  with_unfolding_all exact fold

end DuplicatePrefix.GeneralBorrowWriteCacheFold
