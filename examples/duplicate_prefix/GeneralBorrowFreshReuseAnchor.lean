import duplicate_prefix.GeneralBorrowFreshReuseProtection
import duplicate_prefix.GeneralBorrowFreshAnchor
namespace DuplicatePrefix.GeneralBorrowFreshReuseAnchor
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralBorrowFreshMaterialization
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
private theorem topology_size (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
  unfold_general_projection
  unfold_general_topology
  simp only [Array.size_map]

/-- The reused leaf owns this actual materialized location. Protection equality
is derived from actual tag-table preservation. No condition on stale permissions at the replaced slot is used. -/
theorem anchor_owned (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (fits : tree.nodes.data.size ≤ 4294967296) (parentPresent : tree.nodeAt parent = some parentNode)
    (childParent : newNode.parent = some parent) (leaf : newNode.children = #[])
    (location : LocationTree) (state : LocationState) (protections : ProtectedTags) (kind : AccessKind)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) parent.toNat kind)
    (childOwned : ∀ held, GeneralBorrowPermissions.AccessOwned state kind .LocalAccess held)
 :
    GeneralBorrowAnchor.AnchorOwned
      (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode)
        (materialized location index state) protections) index.toNat kind := by
  let afterTree := GeneralBorrowFreshGraph.attached tree index parent parentNode newNode
  let afterLocation := materialized location index state
  let beforeNormal := source_normal_projection tree location protections
  let afterNormal := source_normal_projection afterTree afterLocation protections
  change GeneralBorrowAnchor.AnchorOwned afterNormal index.toNat kind
  have extension : GeneralBorrowFreshReuseTopology.Extension beforeNormal.topology afterNormal.topology index.toNat parent.toNat :=
    GeneralBorrowFreshReuseProjection.topology_extension tree index parent parentNode newNode bounded vacant parentPresent childParent leaf location afterLocation protections
  have beforeSize : beforeNormal.topology.nodes.size = tree.nodes.data.size := topology_size tree location protections
  have afterSize : afterNormal.topology.nodes.size = tree.nodes.data.size := by rw [extension.length,beforeSize]
  have path : afterNormal.topology.ancestorPath index.toNat = index.toNat :: beforeNormal.topology.ancestorPath parent.toNat :=
    GeneralBorrowFreshReuseProjection.projected_ancestors tree index parent parentNode newNode bounded vacant parentPresent childParent leaf location afterLocation protections forest
  refine ⟨by rw [afterSize];exact bounded,?_,?_,?_⟩
  · dsimp only [afterNormal]
    exact (projection_sizes afterTree afterLocation protections).1.trans (topology_size afterTree afterLocation protections).symm
  · dsimp only [afterNormal]
    exact (projection_sizes afterTree afterLocation protections).2.trans (topology_size afterTree afterLocation protections).symm
  · intro position valid
    by_cases fresh : position = index.toNat
    · subst position
      refine ⟨state,GeneralBorrowFreshReuseState.state_new tree index parent parentNode newNode bounded vacant parentPresent location state protections,?_⟩
      have localAccess : GeneralBorrowAnchor.relation afterNormal index.toNat index.toNat = .LocalAccess := by
        unfold GeneralBorrowAnchor.relation
        rw [path]
        simp
      rw [localAccess]
      exact childOwned _
    · have oldValid : position < tree.nodes.data.size := by rw [afterSize] at valid;omega
      obtain ⟨before,present,permitted⟩ := owned.permissions position (by rw [beforeSize];exact oldValid)
      refine ⟨before,(GeneralBorrowFreshReuseState.state_old tree index parent parentNode newNode bounded vacant parentPresent fits location state protections position oldValid fresh).trans present,?_⟩
      have related : GeneralBorrowAnchor.relation afterNormal index.toNat position =
          GeneralBorrowAnchor.relation beforeNormal parent.toNat position := by
        unfold GeneralBorrowAnchor.relation
        rw [path]
        simp only [List.mem_cons,fresh,false_or]
      have protectionEq : afterNormal.protectedNodes.contains position = beforeNormal.protectedNodes.contains position :=
        GeneralBorrowFreshReuseProtection.protection_position tree index parent parentNode newNode vacant parentPresent
          location afterLocation protections fits position oldValid fresh
      rw [related,protectionEq]
      exact permitted

private theorem mutable_capable (kind : AccessKind) (held : Bool) :
    GeneralBorrowPermissions.AccessOwned GeneralBorrowFreshChild.inside kind .LocalAccess held := by
  cases kind with
  | Read => simp [GeneralBorrowPermissions.AccessOwned,GeneralBorrowPermissions.LocalReadable,
      GeneralBorrowFreshChild.inside,LocationState.possible,Permission.isUnique]
  | Write => exact GeneralBorrowPermissions.fresh_mutable_owned .None true held

/-- Both forest and ownership components of LocationOwned are established for
an actual protected-mutable child at one materialized inside location. -/
theorem mutable_location_owned (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (newTag : BorTag)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (fits : tree.nodes.data.size ≤ 4294967296) (parentPresent : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags) (kind : AccessKind)
    (owned : GeneralBorrowRange.LocationOwned tree protections parent kind location)
 :
    GeneralBorrowRange.LocationOwned
      (GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshChild.child newTag parent))
      protections index kind (materialized location index GeneralBorrowFreshChild.inside) := by
  rcases owned with ⟨⟨forest⟩,owner⟩
  refine ⟨⟨GeneralBorrowFreshReuseProjection.projected_forest tree index parent parentNode (GeneralBorrowFreshChild.child newTag parent)
    bounded vacant parentPresent rfl rfl location (materialized location index GeneralBorrowFreshChild.inside) protections forest⟩,?_⟩
  exact anchor_owned tree index parent parentNode (GeneralBorrowFreshChild.child newTag parent) bounded vacant fits parentPresent rfl rfl
    location GeneralBorrowFreshChild.inside protections kind forest owner (mutable_capable kind)

end DuplicatePrefix.GeneralBorrowFreshReuseAnchor
#print axioms DuplicatePrefix.GeneralBorrowFreshReuseAnchor.anchor_owned

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshReuseAnchor." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved reusable ownership dependency {dependency}"
