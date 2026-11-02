import duplicate_prefix.GeneralBorrowExposureGraphTransport
import duplicate_prefix.GeneralBorrowFreshMetadataChildSifa
import duplicate_prefix.GeneralBorrowSifaCacheFrame
import duplicate_prefix.GeneralRangeMapState
namespace DuplicatePrefix.GeneralBorrowExposureSifaTransport
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposureCardinality DuplicatePrefix.GeneralBorrowExposureAncestorFold
open DuplicatePrefix.GeneralBorrowView DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem mapped_get {α β : Type} (nodes : UniValMap α) (shape : α → β) (index : UniIndex) :
    (UniValMap.get ⟨nodes.data.map (Option.map shape)⟩ index) = (nodes.get index).map shape := by
  simp only [UniValMap.get,Array.getElem?_map]
  cases nodes.data[index.toNat]? <;> rfl

/-- SIFA-erasing permission views determine the actual local access level. -/
theorem effective_same (before after : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (oldNode newNode : TreeNode)
    (same : locationShape after = locationShape before)
    (tag : newNode.tag = oldNode.tag)
    (permission : newNode.defaultInitialPermission = oldNode.defaultInitialPermission) :
    effective after protections index newNode = effective before protections index oldNode := by
  have states : (after.perms.get index).map stateShape = (before.perms.get index).map stateShape := by
    rw [←mapped_get after.perms stateShape index,←mapped_get before.perms stateShape index]
    exact congrArg (fun values => UniValMap.get ⟨values⟩ index) same
  cases old : before.perms.get index <;> cases new : after.perms.get index
  · simp only [effective,old,new,Option.getD_none,TreeNode.defaultLocationState,permission,tag]
  · simp only [old,new,Option.map_none,Option.map_some] at states;cases states
  · simp only [old,new,Option.map_none,Option.map_some] at states;cases states
  · simp only [old,new,Option.map_some] at states
    have permissions := congrArg Prod.fst (Option.some.inj states)
    simpa only [effective,old,new,Option.getD_some,tag,stateShape] using
      congrArg (fun p => p.strongestAllowedLocalAccess (protections.contains oldNode.tag)) permissions

/-- Shape-equivalent trees with identical exposure flags and per-location
permission/cache views retain the actual descendant-count invariant. -/
theorem location (before after : BorrowTree) (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth before.nodes)
    (same : treeShape after = treeShape before)
    (flags : GeneralBorrowFreshMetadataChildSifa.exposureShape after = GeneralBorrowFreshMetadataChildSifa.exposureShape before)
    (oldLocation newLocation : LocationTree) (locations : locationShape newLocation = locationShape oldLocation)
    (cache : newLocation.exposedCache = oldLocation.exposedCache)
    (initial : LocationCoherent before oldLocation protections) : LocationCoherent after newLocation protections := by
  have oldFrame : ∀ index node,before.nodes.get index = some node → ∃ next,after.nodes.get index = some next ∧
      next.parent = node.parent ∧ next.isExposed = node.isExposed ∧
      effective newLocation protections index next = effective oldLocation protections index node := by
    intro index node present
    obtain ⟨next,found,tag,parent,children,permission⟩ := GeneralBorrowFreshMetadata.node_fields before after same index node present
    have flag := GeneralBorrowFreshMetadataChildSifa.lookup_exposure before after flags index
    rw [found,present] at flag
    refine ⟨next,found,parent,?_,effective_same oldLocation newLocation protections index node next locations tag permission⟩
    simpa only [Option.map_some,Option.some.injEq] using flag
  intro query kind
  rw [cache,initial query kind]
  apply congrArg UInt16.ofNat
  apply Eq.symm
  apply GeneralBorrowExposureGraphTransport.extension before.nodes after.nodes depth _ _
    (Nat.le_of_eq (GeneralBorrowFreshMetadata.node_size before after same).symm) oldFrame
  intro index next found exposed
  obtain ⟨node,present,_⟩ := GeneralBorrowFreshMetadata.node_exists after before same.symm index next found
  exact ⟨node,present⟩

/-- Actual ancestor SIFA weakening preserves every range's exposed-support
cache invariant, including its source error branches. -/
theorem sifa (tree : BorrowTree) (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (start : UniIndex) (strongest : IdempotentForeignAccess)
    (initial : Every (fun location => LocationCoherent tree location protections) tree.locations) :
    let result := (sourceUpdateSifa tree start strongest).1
    Every (fun location => LocationCoherent result location protections) result.locations := by
  dsimp only
  let result := (sourceUpdateSifa tree start strongest).1
  have same := GeneralBorrowSifaView.preserves tree start strongest
  have flags := GeneralBorrowFreshMetadataChildSifa.sifa_exposure tree start strongest
  have caches := GeneralBorrowSifaCacheFrame.sifa_cache tree start strongest
  have locations := congrArg (fun shape => shape.2.2.1) same
  change result.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
    tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at locations
  have sizes : result.locations.entries.size = tree.locations.entries.size := by
    simpa only [Array.size_map] using congrArg Array.size locations
  intro position valid
  have oldValid : position < tree.locations.entries.size := by rw [←sizes];exact valid
  have newValid : position < result.locations.entries.size := valid
  have locationEq := congrArg (fun values => values[position]?) locations
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem newValid,Array.getElem?_eq_getElem oldValid,
    Option.map_some,Option.some.injEq,Prod.mk.injEq] at locationEq
  have cacheEq := congrArg (fun values => values[position]?) caches
  change (result.locations.entries.map _)[position]? = (tree.locations.entries.map _)[position]? at cacheEq
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem newValid,Array.getElem?_eq_getElem oldValid,
    Option.map_some,Option.some.injEq,Prod.mk.injEq] at cacheEq
  exact location tree result protections depth same flags _ _ locationEq.2 cacheEq.2 (initial position oldValid)

end DuplicatePrefix.GeneralBorrowExposureSifaTransport
