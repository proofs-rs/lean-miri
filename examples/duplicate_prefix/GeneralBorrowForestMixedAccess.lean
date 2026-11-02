import duplicate_prefix.GeneralBorrowForestForeignAccess
import duplicate_prefix.GeneralBorrowFreshReleaseMixed

namespace DuplicatePrefix.GeneralBorrowForestMixedAccess
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowFreshReleaseMixed (Mixed)
open GeneralBorrowWildcardSubtreeRegion
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Stable shared input retaining per-node mutable/read-only labels. The common
foreign region uses strong ForeignOwned, independently of those labels. -/
structure Data (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (extras : List UniIndex) (writable : Nat → Bool) where
  base : GeneralBorrowForestForeignAccess.LocationData tree location protections anchor primary extras .Read
  mixed : Mixed tree protections anchor writable location
  writeZero : ∀ index, base.region.support index → GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index .Write = 0

private theorem slot (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (position : Nat) (index : UniIndex) (converted : UniIndex.ofNat? position = some index) (equal : index.toNat = position)
    (valid : position < tree.nodes.data.size) :
    (source_normal_projection tree location protections).stateAt position =
      some ((location.perms.get index).getD
        (((tree.nodeAt index).map TreeNode.defaultLocationState).getD ⟨.Disabled,false,.None⟩)) := by
  have nodeValue : tree.nodeAt index = tree.nodes.data[position]'valid := by
    unfold BorrowTree.nodeAt UniValMap.get
    simp only [equal,Array.getElem?_eq_getElem valid]
  unfold_general_projection
  unfold NormalTreeState.stateAt
  simp only [Array.getElem?_mapIdx,Array.getElem?_map,Array.getElem?_eq_getElem valid,converted,Option.map_some]
  rw [nodeValue]
  cases stored : location.perms.get index <;> cases tree.nodes.data[position] <;> rfl

/-- Actual normal Read preserves mixed labels, including its real permission
write-back and cache processing. The caller graph may contain multiple roots. -/
theorem normal_mixed (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (mode : ChildrenVisitMode) (writable : Nat → Bool)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owner : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat .Read)
    (mixed : Mixed tree protections anchor writable location) :
    Mixed tree protections anchor writable (tree.performNormalAccessAt location anchor .Read protections mode).location := by
  let normal := source_normal_projection tree location protections
  have preserved := GeneralBorrowOwnership.normal_preserves normal forest anchor.toNat owner.anchorValid
    .Read mode writable owner.locationsAligned mixed (fun _ _ _ _ => rfl)
  have storage : GeneralBorrowStorage.SameStorage normal (normal.performAccess anchor.toNat .Read mode).tree :=
    GeneralBorrowStorage.events_storage
      (normal.topology.traverse anchor.toNat mode (sourceNormalSkipped normal .Read)).2
      (normal.topology.traverse anchor.toNat mode (sourceNormalSkipped normal .Read)).1 .Read normal
  have relations : GeneralBorrowAnchor.relation (normal.performAccess anchor.toNat .Read mode).tree anchor.toNat =
      GeneralBorrowAnchor.relation normal anchor.toNat := by
    funext position
    unfold GeneralBorrowAnchor.relation
    rw [storage.1]
  unfold Mixed
  rw [GeneralBorrowRangePreserves.normal_projection tree location protections anchor .Read mode fits]
  change GeneralBorrowOwnership.Pointwise (normal.performAccess anchor.toNat .Read mode).tree writable
    (GeneralBorrowAnchor.relation (normal.performAccess anchor.toNat .Read mode).tree anchor.toNat)
  rw [relations]
  exact preserved.2

/-- Strong foreign-region postownership merges with the real normal mixed
poststate, for either writable label. No operation outcome is assumed. -/
theorem merge (tree : BorrowTree) (initial normal after : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (writable : Nat → Bool) (fits : tree.nodes.data.size ≤ 4294967296)
    (region : Region tree initial .Read protections)
    (owned : Mixed tree protections anchor writable normal) (regionOwned : Owned region after)
    (outside : ∀ query, ¬region.support query → after.perms.get query = normal.perms.get query)
    (foreignGraph : ∀ query, region.support query →
      query.toNat ∉ (source_normal_projection tree normal protections).topology.ancestorPath anchor.toNat) :
    Mixed tree protections anchor writable after := by
  unfold Mixed at owned ⊢
  dsimp only [GeneralBorrowOwnership.Pointwise] at owned ⊢
  intro position valid
  have bounded : position < tree.nodes.data.size := by
    rw [(projection_sizes tree after protections).1] at valid
    exact valid
  have normalValid : position < (source_normal_projection tree normal protections).locationStates.size := by
    rw [(projection_sizes tree normal protections).1]
    exact bounded
  obtain ⟨index,converted,equal⟩ := index_nat position (by omega)
  by_cases supported : region.support index
  · obtain ⟨node,present⟩ := region.present index supported
    refine ⟨GeneralBorrowWildcardVirtualLeaf.effective after index node,?_,?_⟩
    · rw [projection_state tree after protections position index node converted equal present]
      rfl
    · have foreign := foreignGraph index supported
      change GeneralBorrowPermissions.Required _ (writable position)
        (if position ∈ (source_normal_projection tree normal protections).topology.ancestorPath anchor.toNat then .LocalAccess else .ForeignAccess) _
      rw [←equal,ite_eq_right foreign,GeneralBorrowForestRegionOwnerMerge.held_present tree after protections index node present]
      cases writable index.toNat <;> exact regionOwned index node supported present
  · obtain ⟨state,present,permitted⟩ := owned position normalValid
    refine ⟨state,?_,permitted⟩
    rw [slot tree after protections position index converted equal bounded,
      outside index supported,←slot tree normal protections position index converted equal bounded]
    exact present

/-- The REAL normal-plus-extra-subtree Read retains mixed mutable/read-only
labels and re-forms the full shared input records. Either visitor mode and
arbitrary finite unexposed foreign subtrees are supported, without a visitor
exclusion or successful-operation premise. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (extras : List UniIndex) (writable : Nat → Bool)
    (mode : ChildrenVisitMode) (range : ByteRange) (context : Context tree anchor primary extras)
    (data : Data tree location protections anchor primary extras writable)
    (fits : tree.nodes.data.size ≤ 4294967296) :
    source_access_status (source_tree_access_at tree location (some anchor) .Read protections mode range) = none ∧
    Nonempty (Data tree (source_access_location (source_tree_access_at tree location (some anchor) .Read protections mode range))
      protections anchor primary extras writable) := by
  obtain ⟨after,actual,status,preserved,cache,frame⟩ := GeneralBorrowWildcardSubtreeForeignIterator.access tree location protections
    anchor primary context.anchorNode context.primaryNode extras .Read mode range data.base.forest data.base.owned context.depth context.children
    context.anchorPresent context.primaryPresent context.roots context.different data.base.rootPath data.base.region data.base.supported fits data.base.foreignGraph
    context.unexposed
  have normalMixed := normal_mixed tree location protections anchor mode writable fits data.base.forest data.base.owned data.mixed
  have retained := merge tree location (tree.performNormalAccessAt location anchor .Read protections mode).location after protections
    anchor writable fits data.base.region normalMixed preserved frame data.base.foreignGraph
  have normalOwner := GeneralBorrowRangePreserves.normal_location_owned tree location protections anchor .Read mode fits data.base.forest data.base.owned
  have retainedOwner := GeneralBorrowForestRegionOwnerMerge.merge tree location
    (tree.performNormalAccessAt location anchor .Read protections mode).location after protections
    anchor .Read .Read fits data.base.region normalOwner preserved frame data.base.foreignGraph
  refine ⟨status,?_⟩
  rw [actual]
  exact ⟨{
    base := {
      forest := data.base.forest
      owned := retainedOwner
      rootPath := data.base.rootPath
      region := rebase data.base.region after preserved cache
      supported := data.base.supported
      foreignGraph := data.base.foreignGraph }
    mixed := retained
    writeZero := by intro index member;rw [cache];exact data.writeZero index member }⟩

end DuplicatePrefix.GeneralBorrowForestMixedAccess
