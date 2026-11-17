import duplicate_prefix.GeneralBorrowGcCacheAtomic

namespace DuplicatePrefix.GeneralBorrowGcSurvivingPaths
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureAncestorFold
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

def Relation (original current : UniValMap TreeNode) : Prop :=
  ∀ source node,current.get source = some node → ∀ query value,current.get query = some value →
    (query ∈ walk current (current.size+1) source ↔ query ∈ walk original (original.size+1) source)

def Valid (original current : UniValMap TreeNode) : Prop :=
  ∃ depth : ParentDepth current, Relation original current

theorem initial (nodes : UniValMap TreeNode) (depth : ParentDepth nodes) : Valid nodes nodes :=
  ⟨depth,by intro source node found query value present;rfl⟩

/-- Exact surviving ancestry composes through an actual sparse contraction.
The removed node itself may have arbitrary descendants; only surviving queries
are compared. All traversal budgets are derived from bounded OLD data ranks. -/
theorem contract (original before after : UniValMap TreeNode) (removed : UniIndex) (node : TreeNode)
    (data : GeneralBorrowGcCacheContraction.Contract before after removed node)
    (good : Valid original before) : Valid original after := by
  obtain ⟨depth,relation⟩ := good
  refine ⟨data.depth depth,?_⟩
  intro source value found query queryNode queryFound
  obtain ⟨different,old,present⟩ := data.backward source value found
  obtain ⟨queryDifferent,oldQuery,queryPresent⟩ := data.backward query queryNode queryFound
  exact (GeneralBorrowGcCacheContraction.walk_member data depth (before.size+1) (after.size+1) source old present different
    (by have := depth.bounded source old present;omega)
    (by have := depth.bounded source old present;have := data.size;omega) query queryDifferent).trans
      (relation source old present query oldQuery queryPresent)

/-- A present-node child-array update has no effect on actual parent paths. -/
theorem children (original nodes : UniValMap TreeNode) (index : UniIndex) (node : TreeNode)
    (present : nodes.get index = some node) (kept : Array UniIndex) (good : Valid original nodes) :
    Valid original (nodes.insert index {node with children := kept}) := by
  obtain ⟨depth,relation⟩ := good
  let after := nodes.insert index {node with children := kept}
  have size : after.size = nodes.size := GeneralBorrowNodeUpdate.insert_existing_size nodes index node _ present
  have forward : ∀ query old,nodes.get query = some old → ∃ next,after.get query = some next ∧ next.parent = old.parent := by
    intro query old found
    by_cases same : query = index
    · subst query
      have equal := Option.some.inj (present.symm.trans found)
      subst old
      exact ⟨_,GeneralBorrowNodeUpdate.insert_existing_get_same nodes index node _ present,rfl⟩
    · exact ⟨old,(GeneralBorrowNodeUpdate.insert_existing_get_other nodes index query node _ present same).trans found,rfl⟩
  have back : ∀ query next,after.get query = some next → ∃ old,nodes.get query = some old ∧ next.parent = old.parent := by
    intro query next found
    by_cases same : query = index
    · subst query
      rw [GeneralBorrowNodeUpdate.insert_existing_get_same nodes index node _ present] at found
      cases found
      exact ⟨node,present,rfl⟩
    · rw [GeneralBorrowNodeUpdate.insert_existing_get_other nodes index query node _ present same] at found
      exact ⟨next,found,rfl⟩
  have newDepth : ParentDepth after := by
    refine ⟨depth.depth,?_,?_⟩
    · intro query next found
      obtain ⟨old,oldFound,_⟩ := back query next found
      rw [size]
      exact depth.bounded query old oldFound
    · intro query next found parent edge
      obtain ⟨old,oldFound,parentSame⟩ := back query next found
      obtain ⟨oldParent,parentFound,smaller⟩ := depth.parent query old oldFound parent (parentSame.symm.trans edge)
      obtain ⟨newParent,newFound,_⟩ := forward parent oldParent parentFound
      exact ⟨newParent,newFound,smaller⟩
  refine ⟨newDepth,?_⟩
  intro source value found query queryNode queryFound
  obtain ⟨old,present,_⟩ := back source value found
  obtain ⟨oldQuery,queryPresent,_⟩ := back query queryNode queryFound
  rw [GeneralBorrowExposureGraphTransport.walk_extension nodes after depth forward (nodes.size+1) (after.size+1) source old present
    (by have := depth.bounded source old present;omega) (by have := depth.bounded source old present;rw [size];omega)]
  exact relation source old present query oldQuery queryPresent

end DuplicatePrefix.GeneralBorrowGcSurvivingPaths
