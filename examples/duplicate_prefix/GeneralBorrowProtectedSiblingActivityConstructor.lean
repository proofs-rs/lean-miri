import duplicate_prefix.GeneralBorrowProtectedSiblingPartialActive
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableReuse
import duplicate_prefix.GeneralBorrowGcVacantClean
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingActivityConstructor
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshActiveWithin GeneralRangeMapOrigins GeneralRangeMapState GeneralBorrowFreshMaterialization
open GeneralBorrowFreshInstallation GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Installing a different slot preserves an earlier slot's exact stored state
and hence its strict bytewise activity bounds, for arbitrary window overlap. -/
theorem modified (tree : BorrowTree) (index query : UniIndex) (state : LocationState) (ownerKind : AccessKind)
    (offset len : Size) (lower upper : UInt64) (different : query ≠ index)
    (well : tree.locations.WellFormed) (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (active : ActiveWithin tree query ownerKind lower upper) :
    ActiveWithin {tree with locations := (tree.locations.modifyRange offset len (fun _ location => materialized location index state)).state}
      query ownerKind lower upper := by
  let modify := fun (_ : ByteRange) location => materialized location index state
  let prepared := tree.locations.iterMut offset len
  let updated := (tree.locations.modifyRange offset len modify).state
  have preparedData := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have preparedActive := refines tree.locations prepared.state preparedData.2.1 query ownerKind lower upper active
  have sizes : updated.entries.size = prepared.state.entries.size := by
    dsimp only [updated,prepared]
    rw [GeneralBorrowFreshModify.state_exact tree.locations offset len modify well bounds,GeneralBorrowFreshModify.fold_size]
  intro point location atPoint old stored accessed kind associated
  obtain ⟨position,valid,startPoint,pointStop,dataEq⟩ := atPoint
  rw [←dataEq] at stored
  have preparedValid : position < prepared.state.entries.size := by change position < updated.entries.size at valid;rw [sizes] at valid;exact valid
  obtain ⟨outputValid,entry⟩ := GeneralBorrowFreshModify.entry_exact tree.locations offset len modify
    (fun _ location => materialized_idempotent location index state) well bounds position preparedValid
  change updated.entries[position] = (if position ∈ prepared.positions.toList then
    {prepared.state.entries[position] with data := modify prepared.state.entries[position].range prepared.state.entries[position].data}
    else prepared.state.entries[position]) at entry
  change updated.entries[position].data.perms.get query = some old at stored
  by_cases selected : position ∈ prepared.positions.toList
  · simp only [selected,↓reduceIte] at entry
    rw [entry] at stored startPoint pointStop
    change ((prepared.state.entries[position].data.perms.insert index state).get query) = some old at stored
    rw [GeneralBorrowFreshLocation.get_other _ index query state different] at stored
    exact preparedActive point prepared.state.entries[position].data ⟨position,preparedValid,startPoint,pointStop,rfl⟩ old stored accessed kind associated
  · simp only [selected,↓reduceIte] at entry
    rw [entry] at stored startPoint pointStop
    exact preparedActive point prepared.state.entries[position].data ⟨position,preparedValid,startPoint,pointStop,rfl⟩ old stored accessed kind associated

theorem append (input : GeneralBorrowFreshMetadataChildMutable.Input) (query : UniIndex) (node : TreeNode)
    (present : input.tree.nodeAt query = some node) (ownerKind : AccessKind) (lower upper : UInt64)
    (active : ActiveWithin input.tree query ownerKind lower upper) :
    ActiveWithin (GeneralBorrowFreshMetadataChildMutable.result input) query ownerKind lower upper := by
  have different : query ≠ GeneralBorrowFreshMetadataChildMutable.index input := by
    intro same
    have bound := (array_of_node input.tree query node present).1
    rw [same,GeneralBorrowFreshMetadataChildMutable.at_end input] at bound
    omega
  rw [GeneralBorrowFreshMetadataChildMutable.tree_eq]
  apply sifa_preserves
  exact modified input.tree (GeneralBorrowFreshMetadataChildMutable.index input) query GeneralBorrowFreshChild.inside ownerKind
    (Size.ofBytes input.offset) (Size.ofBytes input.len) lower upper different input.well input.bounds active

theorem reuse (input : GeneralBorrowFreshMetadataChildMutableReuse.Input) (query : UniIndex) (node : TreeNode)
    (present : input.tree.nodeAt query = some node) (ownerKind : AccessKind) (lower upper : UInt64)
    (active : ActiveWithin input.tree query ownerKind lower upper) :
    ActiveWithin (GeneralBorrowFreshMetadataChildMutableReuse.result input) query ownerKind lower upper := by
  have different : query ≠ GeneralBorrowFreshMetadataChildMutableReuse.index input := by
    intro same
    have vacant := input.vacant
    change input.tree.nodes.get (GeneralBorrowFreshMetadataChildMutableReuse.index input) = none at vacant
    rw [←same] at vacant
    rw [show input.tree.nodes.get query = some node from present] at vacant
    cases vacant
  rw [GeneralBorrowFreshMetadataChildMutableReuse.tree_eq]
  apply sifa_preserves
  exact modified input.tree (GeneralBorrowFreshMetadataChildMutableReuse.index input) query GeneralBorrowFreshChild.inside ownerKind
    (Size.ofBytes input.offset) (Size.ofBytes input.len) lower upper different input.well input.bounds active

/-- Real leading Read followed by real protected append preserves an older
child's strict activity window. Preparation and constructor completion are
formed from raw readable and vacant-slot data, never assumed. -/
theorem read_append (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (roots : input.tree.roots = #[input.parent])
    (readable : Every (GeneralBorrowProtectedReadRelease.Profile input.tree protections) input.tree.locations)
    (clean : GeneralBorrowGcVacantClean.VacantClean input.tree)
    (query : UniIndex) (node : TreeNode) (present : input.tree.nodeAt query = some node) (parent : node.parent = some input.parent)
    (lower upper : UInt64) (active : ActiveWithin input.tree query .Write lower upper) :
    ActiveWithin (GeneralBorrowProtectedReadableStage.child input protections).tree query .Write lower upper := by
  have vacant : input.tree.nodes.get (GeneralBorrowFreshMetadataChildMutable.index input) = none := by
    simp [UniValMap.get,GeneralBorrowFreshMetadataChildMutable.at_end input]
  have slotClean := clean _ vacant
  let prepared := GeneralBorrowProtectedReadableStage.prepare input protections roots readable slotClean
  have afterRead := GeneralBorrowProtectedSiblingPartialActive.read input protections roots readable query node present parent lower upper active
  have frame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read protections .VisitChildrenOfAccessed
  change (GeneralBorrowProtectedReadableStage.read input protections).tree = {input.tree with locations := (GeneralBorrowProtectedReadableStage.read input protections).tree.locations} at frame
  have nextPresent : prepared.next.tree.nodeAt query = some node := by rw [prepared.tree,frame];exact present
  have nextActive : ActiveWithin prepared.next.tree query .Write lower upper := by rw [prepared.tree];exact afterRead
  have kept := append prepared.next query node nextPresent .Write lower upper nextActive
  rw [prepared.result] at kept
  exact kept
end DuplicatePrefix.GeneralBorrowProtectedSiblingActivityConstructor
