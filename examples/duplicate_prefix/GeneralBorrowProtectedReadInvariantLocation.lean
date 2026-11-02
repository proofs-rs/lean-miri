import duplicate_prefix.GeneralBorrowProtectedReadInvariant
import duplicate_prefix.GeneralBorrowProtectedReadSingleRoot
namespace DuplicatePrefix.GeneralBorrowProtectedReadInvariantLocation
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowProtectedReadInvariant
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def Data (tree : BorrowTree) (protections : ProtectedTags) (location : LocationTree) : Prop :=
  GeneralBorrowProtectedReadInvariant.Data (source_normal_projection tree location protections)

theorem location (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor root : UniIndex) (mode : ChildrenVisitMode) (range : ByteRange)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (fits : tree.nodes.data.size ≤ 4294967296) (depth : ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (node : TreeNode) (present : tree.nodeAt anchor = some node)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (initial : Data tree protections location) :
    source_access_status (source_tree_access_at tree location (some anchor) .Read protections mode range) = none ∧
      Data tree protections (source_access_location (source_tree_access_at tree location (some anchor) .Read protections mode range)) := by
  let normal := source_normal_projection tree location protections
  have valid : anchor.toNat < normal.topology.nodes.size := by
    obtain ⟨valid,_⟩ := array_of_node tree anchor node present
    dsimp only [normal];unfold_general_projection;unfold_general_topology
    simpa only [Array.size_mapIdx,Array.size_map] using valid
  have aligned : normal.locationStates.size = normal.topology.nodes.size := by
    dsimp only [normal];unfold_general_projection;unfold_general_topology
    simp only [Array.size_mapIdx,Array.size_map]
  change GeneralBorrowProtectedReadInvariant.Data normal at initial
  have compatible : ∀ index,index < normal.topology.nodes.size → ∃ state,normal.stateAt index = some state ∧
      GeneralBorrowProtectedReadCompatible.Compatible state (GeneralBorrowAnchor.relation normal anchor.toNat index)
        (normal.protectedNodes.contains index) := by
    intro index bounded
    obtain ⟨state,stored,good⟩ := initial index (by omega)
    exact ⟨state,stored,GeneralBorrowProtectedReadInvariant.compatible state _ _ good⟩
  refine ⟨GeneralBorrowProtectedReadSingleRoot.access_at tree location protections anchor root mode range forest valid compatible
    depth children node present roots covered,?_⟩
  rw [GeneralBorrowProtectedReadSingleRoot.single_root_location tree location protections anchor root mode range forest valid compatible
    depth children node present roots covered]
  unfold Data
  rw [GeneralBorrowRangePreserves.normal_projection tree location protections anchor .Read mode fits]
  exact (GeneralBorrowProtectedReadInvariant.normal normal forest anchor.toNat valid mode aligned initial).2
end DuplicatePrefix.GeneralBorrowProtectedReadInvariantLocation
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedReadInvariantLocation.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected Read invariant location dependency {dependency}"
