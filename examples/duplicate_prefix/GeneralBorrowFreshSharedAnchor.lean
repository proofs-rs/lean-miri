import duplicate_prefix.GeneralBorrowFreshReuseAnchor
namespace DuplicatePrefix.GeneralBorrowFreshSharedAnchor
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshAnchor DuplicatePrefix.GeneralBorrowFreshMaterialization
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- The Frozen shared child owns one actual materialized location when using
a reusable slot. The parent supplies Read ownership, and old permissions at
the replaced slot may be arbitrary because its inside state is overwritten. -/
theorem reuse_location_owned (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (newTag : BorTag)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (fits : tree.nodes.data.size ≤ 4294967296) (parentPresent : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags)
    (owned : GeneralBorrowRange.LocationOwned tree protections parent .Read location) :
    GeneralBorrowRange.LocationOwned
      (GeneralBorrowFreshGraph.attached tree index parent parentNode (sharedNode newTag parent))
      protections index .Read (materialized location index sharedState) := by
  rcases owned with ⟨⟨forest⟩,owner⟩
  refine ⟨⟨GeneralBorrowFreshReuseProjection.projected_forest tree index parent parentNode (sharedNode newTag parent)
    bounded vacant parentPresent rfl rfl location (materialized location index sharedState) protections forest⟩,?_⟩
  apply GeneralBorrowFreshReuseAnchor.anchor_owned tree index parent parentNode (sharedNode newTag parent)
    bounded vacant fits parentPresent rfl rfl location sharedState protections .Read forest owner
  intro held
  exact GeneralBorrowPermissions.fresh_shared_readable .Read true
end DuplicatePrefix.GeneralBorrowFreshSharedAnchor
#print axioms DuplicatePrefix.GeneralBorrowFreshSharedAnchor.reuse_location_owned
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshSharedAnchor." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved frozen anchor dependency {dependency}"
