import duplicate_prefix.GeneralBorrowWildcardSubtreeData
import duplicate_prefix.GeneralBorrowFreshLocation

namespace DuplicatePrefix.GeneralBorrowWildcardSubtreeState
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardVirtualLeaf (effective)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def Owned {tree : BorrowTree} {initial : LocationTree} {root : UniIndex}
    {kind : AccessKind} {protections : ProtectedTags}
    (data : GeneralBorrowWildcardSubtreeData.Data tree initial root kind protections)
    (location : LocationTree) : Prop :=
  ∀ index node, data.support index → tree.nodes.get index = some node →
    GeneralBorrowPermissions.ForeignOwned (effective location index node) (protections.contains node.tag)

def write (location : LocationTree) (index : UniIndex) (node : TreeNode)
    (recorded next : LocationState) : LocationTree :=
  {location with perms := ((location.perms.orInsert index node.defaultLocationState).1.insert index recorded).insert index next}

theorem or_insert_snd (location : LocationTree) (index : UniIndex) (node : TreeNode) :
    (location.perms.orInsert index node.defaultLocationState).2 = effective location index node := by
  cases stored : location.perms.get index <;> simp only [UniValMap.orInsert,effective,stored,Option.getD]

theorem write_same (location : LocationTree) (index : UniIndex) (node : TreeNode)
    (recorded next : LocationState) : (write location index node recorded next).perms.get index = some next := by
  dsimp only [write]
  exact GeneralBorrowFreshLocation.get_same ((location.perms.orInsert index node.defaultLocationState).1.insert index recorded) index next

theorem write_other (location : LocationTree) (index query : UniIndex) (node : TreeNode)
    (recorded next : LocationState) (different : query ≠ index) :
    (write location index node recorded next).perms.get query = location.perms.get query := by
  dsimp only [write]
  rw [GeneralBorrowFreshLocation.get_other _ index query next different,
    GeneralBorrowFreshLocation.get_other _ index query recorded different]
  unfold UniValMap.orInsert
  split
  · rfl
  · exact GeneralBorrowFreshLocation.get_other _ index query node.defaultLocationState different

theorem owned_write {tree : BorrowTree} {initial : LocationTree} {root : UniIndex}
    {kind : AccessKind} {protections : ProtectedTags}
    (data : GeneralBorrowWildcardSubtreeData.Data tree initial root kind protections)
    (location : LocationTree) (index : UniIndex) (node : TreeNode) (recorded next : LocationState)
    (present : tree.nodes.get index = some node) (owned : Owned data location)
    (newOwned : GeneralBorrowPermissions.ForeignOwned next (protections.contains node.tag)) :
    Owned data (write location index node recorded next) := by
  intro query queryNode supported queryPresent
  by_cases same : query = index
  · subst query
    have nodeEq := Option.some.inj (present.symm.trans queryPresent)
    subst queryNode
    simpa only [effective,write_same,Option.getD_some] using newOwned
  · simpa only [effective,write_other location index query node recorded next same] using
      owned query queryNode supported queryPresent

end DuplicatePrefix.GeneralBorrowWildcardSubtreeState
