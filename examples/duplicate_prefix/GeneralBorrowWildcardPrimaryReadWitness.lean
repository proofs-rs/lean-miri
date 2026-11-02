import duplicate_prefix.GeneralBorrowWildcardControlReadWitness
namespace DuplicatePrefix.GeneralBorrowWildcardPrimaryReadWitness
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardControlWitness
open DuplicatePrefixCallbackAuthorization
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A designated physical-root Read witness, with no permission profile. -/
structure Data (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags) (root : UniIndex) where
  witness : UniIndex
  node : TreeNode
  present : tree.nodes.get witness = some node
  supports : Supports initial protections witness node none .Read
  path : Path tree root witness

def PointwiseReadFrame (tree : BorrowTree) (protections : ProtectedTags) (before after : LocationTree) : Prop :=
  ∀ index node, tree.nodes.get index = some node →
    (GeneralBorrowExposureCardinality.effective after protections index node).allows .Read =
    (GeneralBorrowExposureCardinality.effective before protections index node).allows .Read

/-- S01's witness and Covers data form a real child-reachable witness. -/
theorem of_authorization (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (support : UniIndex → Prop)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (authorization : DuplicatePrefixResidualSupportAuthorization.Authorization tree initial protections root 0 none .Read support) :
    Nonempty (Data tree initial protections root) := by
  obtain ⟨index,node,included,present,witness⟩ := authorization.witness rfl
  exact ⟨⟨index,node,present,witness,path_of_covers tree depth root index node present (authorization.covers index included)⟩⟩

/-- Pointwise Read-support preservation retains the same designated witness;
counter-only ReadFrame would not justify this assertion. -/
theorem supports_current {tree initial protections root} (data : Data tree initial protections root)
    (current : LocationTree) (frame : PointwiseReadFrame tree protections initial current) :
    Supports current protections data.witness data.node none .Read := by
  refine ⟨data.supports.1,?_,rfl⟩
  change (GeneralBorrowExposureCardinality.effective current protections data.witness data.node).allows .Read = true
  rw [frame data.witness data.node data.present]
  exact data.supports.2.1

/-- The actual raw callback witness test succeeds at this designated node. -/
theorem found_current {tree initial protections root} (data : Data tree initial protections root)
    (current : LocationTree) (frame : PointwiseReadFrame tree protections initial current) :
    (data.node.isExposed &&
      (((current.perms.get data.witness).getD data.node.defaultLocationState).permission.strongestAllowedLocalAccess
        (protections.contains data.node.tag)).allows .Read &&
      ((none : Option BorTag).isNone || (none : Option BorTag).any (fun tag => tag.value >= data.node.tag.value))) = true :=
  (supports_source current protections data.witness data.node none .Read).mp (supports_current data current frame)

end DuplicatePrefix.GeneralBorrowWildcardPrimaryReadWitness
