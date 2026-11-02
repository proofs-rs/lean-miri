import duplicate_prefix.GeneralBorrowProtectedReadPermissionMetadata
import duplicate_prefix.GeneralBorrowReadUnique
import duplicate_prefix.GeneralBorrowFreshSharedPaths
import duplicate_prefix.GeneralBorrowTerminal
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingRootRead
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowExposure BorrowRangeAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The actual normal Read from any node in a covered singleton-root forest
retains the stored Unique permission of that root. Event relatedness follows
from the source traversal and terminal ancestor, without ownership premises. -/
theorem normal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor root : UniIndex) (anchorNode rootNode : TreeNode) (mode : ChildrenVisitMode)
    (anchorPresent : tree.nodeAt anchor = some anchorNode) (rootPresent : tree.nodeAt root = some rootNode)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (depth : ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (unique : ∃ state,location.perms.get root = some state ∧ state.permission = .Unique) :
    ∃ state,(tree.performNormalAccessAt location anchor .Read protections mode).location.perms.get root = some state ∧ state.permission = .Unique := by
  let normal := source_normal_projection tree location protections
  have valid := GeneralBorrowProtectedReadPermissionMetadata.valid_anchor tree location protections anchor anchorNode anchorPresent
  have lastRoot := GeneralBorrowTerminal.ancestor_root_present normal.topology forest (GeneralBorrowGraph.Present tree)
    (GeneralBorrowGraph.parents_closed tree location protections depth) anchor.toNat root.toNat valid
    ⟨anchor,anchorNode,rfl,anchorPresent⟩
    (fun index _ present parentless => GeneralBorrowGraph.unique_root tree location protections root roots covered index present parentless)
  have nonempty : normal.topology.ancestorPath anchor.toNat ≠ [] := GeneralBorrowTerminal.ancestors_nonempty _ _ _
  have rootMember : root.toNat ∈ normal.topology.ancestorPath anchor.toNat := by
    rw [←lastRoot,List.getLast!_eq_getLast?_getD,List.getLast?_eq_some_getLast nonempty]
    exact List.getLast_mem nonempty
  apply GeneralBorrowReadUnique.normal_unique tree location protections anchor root rootNode mode rootPresent unique
  intro event member same
  have schedule := GeneralBorrowTraversal.traversal_data normal.topology forest anchor.toNat valid mode (sourceNormalSkipped normal .Read)
  rw [(schedule.2 event member).2,same]
  simp only [rootMember,↓reduceIte]
end DuplicatePrefix.GeneralBorrowProtectedSiblingRootRead
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedSiblingRootRead.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved root Read dependency {dependency}"
