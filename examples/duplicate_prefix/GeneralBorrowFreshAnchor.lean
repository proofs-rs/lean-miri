import duplicate_prefix.GeneralBorrowFreshMaterialization
import duplicate_prefix.GeneralBorrowFreshChild
namespace DuplicatePrefix.GeneralBorrowFreshAnchor
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralBorrowFreshMaterialization
set_option maxRecDepth 65536
set_option maxHeartbeats 100000

private theorem topology_size (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
  unfold_general_projection
  unfold_general_topology
  simp only [Array.size_map]

/-- The actual fresh-leaf topology and materialized location move ownership
from the parent to the child at this one location. No ownership assumption is
made about locations outside the requested borrow range. -/
theorem anchor_owned (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (childParent : newNode.parent = some parent) (leaf : newNode.children = #[])
    (location : LocationTree) (state : LocationState) (protections : ProtectedTags) (kind : AccessKind)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) parent.toNat kind)
    (childOwned : ∀ held, GeneralBorrowPermissions.AccessOwned state kind .LocalAccess held) :
    GeneralBorrowAnchor.AnchorOwned
      (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode)
        (materialized location index state) protections) index.toNat kind := by
  let afterTree := GeneralBorrowFreshGraph.attached tree index parent parentNode newNode
  let afterLocation := materialized location index state
  let beforeNormal := source_normal_projection tree location protections
  let afterNormal := source_normal_projection afterTree afterLocation protections
  change GeneralBorrowAnchor.AnchorOwned afterNormal index.toNat kind
  have extension : GeneralBorrowFreshTopology.Extension beforeNormal.topology afterNormal.topology parent.toNat :=
    GeneralBorrowFreshProjection.topology_extension tree index parent parentNode newNode atEnd parentPresent childParent leaf location afterLocation protections
  have beforeSize : beforeNormal.topology.nodes.size = tree.nodes.data.size := topology_size tree location protections
  have afterSize : afterNormal.topology.nodes.size = tree.nodes.data.size+1 := by rw [extension.length,beforeSize]
  have path : afterNormal.topology.ancestorPath index.toNat = index.toNat :: beforeNormal.topology.ancestorPath parent.toNat :=
    GeneralBorrowFreshProjection.projected_ancestors tree index parent parentNode newNode atEnd parentPresent childParent leaf location afterLocation protections forest
  refine ⟨by rw [afterSize];omega,?_,?_,?_⟩
  · dsimp only [afterNormal]
    exact (projection_sizes afterTree afterLocation protections).1.trans (topology_size afterTree afterLocation protections).symm
  · dsimp only [afterNormal]
    exact (projection_sizes afterTree afterLocation protections).2.trans (topology_size afterTree afterLocation protections).symm
  · intro position valid
    by_cases fresh : position = index.toNat
    · subst position
      refine ⟨state,state_new tree index parent parentNode newNode atEnd parentPresent location state protections,?_⟩
      have localAccess : GeneralBorrowAnchor.relation afterNormal index.toNat index.toNat = .LocalAccess := by
        unfold GeneralBorrowAnchor.relation
        rw [path]
        simp
      rw [localAccess]
      exact childOwned _
    · have oldValid : position < tree.nodes.data.size := by rw [afterSize] at valid;omega
      obtain ⟨before,present,permitted⟩ := owned.permissions position (by rw [beforeSize];exact oldValid)
      refine ⟨before,(state_old tree index parent parentNode newNode atEnd parentPresent location state protections position oldValid).trans present,?_⟩
      have related : GeneralBorrowAnchor.relation afterNormal index.toNat position =
          GeneralBorrowAnchor.relation beforeNormal parent.toNat position := by
        unfold GeneralBorrowAnchor.relation
        rw [path]
        simp only [List.mem_cons,fresh,false_or]
      have protectionEq : afterNormal.protectedNodes.contains position = beforeNormal.protectedNodes.contains position :=
        protection_old tree index parent parentNode newNode atEnd parentPresent location afterLocation protections position oldValid
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
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags) (kind : AccessKind)
    (owned : GeneralBorrowRange.LocationOwned tree protections parent kind location) :
    GeneralBorrowRange.LocationOwned
      (GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshChild.child newTag parent))
      protections index kind (materialized location index GeneralBorrowFreshChild.inside) := by
  rcases owned with ⟨⟨forest⟩,owner⟩
  refine ⟨⟨GeneralBorrowFreshProjection.projected_forest tree index parent parentNode (GeneralBorrowFreshChild.child newTag parent)
    atEnd parentPresent rfl rfl location (materialized location index GeneralBorrowFreshChild.inside) protections forest⟩,?_⟩
  exact anchor_owned tree index parent parentNode (GeneralBorrowFreshChild.child newTag parent) atEnd parentPresent rfl rfl
    location GeneralBorrowFreshChild.inside protections kind forest owner (mutable_capable kind)

/-- Mutable ownership supplies the weaker local read contract needed when a
shared child is created from the same parent. Foreign compatibility is kept. -/
theorem write_readable (state : LocationState) (related : AccessRelatedness) (held : Bool)
    (owned : GeneralBorrowPermissions.AccessOwned state .Write related held) :
    GeneralBorrowPermissions.AccessOwned state .Read related held := by
  cases related with
  | ForeignAccess => exact owned
  | LocalAccess =>
    rcases owned with ⟨possible,permitted⟩
    refine ⟨possible,?_⟩
    intro disabled
    rw [disabled] at permitted
    cases permitted

theorem anchor_readable (tree : NormalTreeState) (anchor : Nat)
    (owned : GeneralBorrowAnchor.AnchorOwned tree anchor .Write) : GeneralBorrowAnchor.AnchorOwned tree anchor .Read := by
  refine ⟨owned.anchorValid,owned.locationsAligned,owned.defaultsAligned,?_⟩
  intro position valid
  obtain ⟨state,present,permitted⟩ := owned.permissions position valid
  exact ⟨state,present,write_readable state _ _ permitted⟩

def sharedNode (tag : BorTag) (parent : UniIndex) : TreeNode := {
  tag,parent := some parent,children := #[],defaultInitialPermission := .Frozen,
  defaultInitialSifa := .Read,isExposed := false }
def sharedState : LocationState := ⟨.Frozen,true,.Read⟩

/-- The corresponding single-location transfer for a protected shared child.
This statement concerns actual node/per-location insertion, not the whole retag. -/
theorem shared_location_owned (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (newTag : BorTag)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags)
    (owned : GeneralBorrowRange.LocationOwned tree protections parent .Read location) :
    GeneralBorrowRange.LocationOwned
      (GeneralBorrowFreshGraph.attached tree index parent parentNode (sharedNode newTag parent))
      protections index .Read (materialized location index sharedState) := by
  rcases owned with ⟨⟨forest⟩,owner⟩
  refine ⟨⟨GeneralBorrowFreshProjection.projected_forest tree index parent parentNode (sharedNode newTag parent)
    atEnd parentPresent rfl rfl location (materialized location index sharedState) protections forest⟩,?_⟩
  apply anchor_owned tree index parent parentNode (sharedNode newTag parent) atEnd parentPresent rfl rfl
    location sharedState protections .Read forest owner
  intro held
  exact GeneralBorrowPermissions.fresh_shared_readable .Read true

end DuplicatePrefix.GeneralBorrowFreshAnchor
#print axioms DuplicatePrefix.GeneralBorrowFreshAnchor.mutable_location_owned
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshAnchor." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved fresh anchor dependency {dependency}"
