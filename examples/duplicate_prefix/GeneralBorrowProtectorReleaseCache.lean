import duplicate_prefix.GeneralBorrowProtectorCacheMap
import duplicate_prefix.GeneralBorrowNormalExposureCache
import duplicate_prefix.GeneralBorrowReleaseProperty
namespace DuplicatePrefix.GeneralBorrowProtectorReleaseCache
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowExposureCardinality
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

/-- Full real protector release for an unexposed source in an arbitrary
single-root forest preserves every cache, including arbitrary exposed nodes
elsewhere. Initial active ranges and ownership derive all associated accesses;
no release/access success is assumed. Coherence holds both under the still-current global protector table and
the removed-tag table, supporting later global bookkeeping removal. -/
theorem release (tree : BorrowTree) (protections : ProtectedTags) (anchor root : UniIndex)
    (ownerKind : AccessKind) (lower upper : UInt64) (positive : lower.toNat < upper.toNat)
    (fits : tree.nodes.data.size ≤ 4294967296) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode) (hidden : anchorNode.isExposed = false)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (tagged : tree.indexOfTag anchorNode.tag = some anchor)
    (nodeTags : ∀ index node,tree.nodeAt index = some node → tree.indexOfTag node.tag = some index)
    (active : GeneralBorrowFreshReleaseLoop.ActiveOn tree anchor ownerKind lower upper)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections anchor ownerKind) lower upper tree.locations)
    (initial : Every (fun location => LocationCoherent tree location protections) tree.locations) :
    let result := tree.releaseProtector anchorNode.tag protections
    result.status = .Released ∧ result.tree = {tree with locations := result.tree.locations} ∧
      Every (fun location => LocationCoherent result.tree location protections) result.tree.locations ∧
      Every (fun location => LocationCoherent result.tree location (protections.remove anchorNode.tag)) result.tree.locations := by
  dsimp only
  let result := tree.releaseProtector anchorNode.tag protections
  let predicate := fun location => LocationCoherent tree location protections
  have step : ∀ location range kind,predicate location → GeneralBorrowRange.LocationOwned tree protections anchor ownerKind location →
      (ownerKind = .Read → kind = .Read) →
      predicate (source_access_location (source_tree_access_at tree location (some anchor) kind protections .SkipChildrenOfAccessed range)) := by
    intro location range kind coherent permission allowed
    obtain ⟨⟨forest⟩,owner⟩ := permission
    have accessOwner := GeneralBorrowRangePreserves.owned_for_access _ anchor.toNat kind ownerKind allowed owner
    have updated := GeneralBorrowNormalExposureCache.access tree location protections anchor kind .SkipChildrenOfAccessed
      depth children anchorNode present forest accessOwner coherent
    rw [GeneralBorrowRangePreserves.single_root_location tree location protections anchor root kind .SkipChildrenOfAccessed range
      forest accessOwner depth children anchorNode present roots covered]
    exact updated.2.2
  have released := GeneralBorrowReleaseProperty.preserves tree protections anchorNode.tag anchor root ownerKind lower upper positive
    fits depth children anchorNode present hidden roots covered tagged active predicate initial step owned
  have nodes : result.tree.nodes = tree.nodes := by simpa only using congrArg BorrowTree.nodes released.2.1
  have beforeAll : Every (fun location => LocationCoherent result.tree location protections) result.tree.locations := by
    intro position valid
    change Coherent _ result.tree.nodes _
    rw [nodes]
    exact released.2.2 position valid
  refine ⟨released.1,released.2.1,beforeAll,?_⟩
  intro position valid
  change LocationCoherent result.tree _ (protections.remove anchorNode.tag)
  have before := beforeAll position valid
  apply GeneralBorrowProtectorCacheMap.remove_hidden result.tree _ protections anchorNode.tag before
  intro query node found same
  have oldFound : tree.nodeAt query = some node := by
    change result.tree.nodes.get query = some node at found
    rw [nodes] at found
    exact found
  have lookup := nodeTags query node oldFound
  rw [same,tagged] at lookup
  have queryEq : query = anchor := (Option.some.inj lookup).symm
  subst query
  have nodeEq : node = anchorNode := Option.some.inj (oldFound.symm.trans present)
  exact nodeEq ▸ hidden

end DuplicatePrefix.GeneralBorrowProtectorReleaseCache
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectorReleaseCache.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved full protector-release cache dependency {dependency}"
