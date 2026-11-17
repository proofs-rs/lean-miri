import duplicate_prefix.GeneralBorrowGcAllocatorFull
import duplicate_prefix.GeneralBorrowTagMap

namespace DuplicatePrefix.GeneralBorrowGcResourceFrame
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

set_option autoImplicit false in
/-- GC may free nodes but does not consume reserved tags or enlarge sparse
storage, and retains the ordered root-index array. -/
structure Frame {n : Nat} (reserve : Fin n → BorTag) (before after : BorrowTree) : Prop where
  fresh : ∀ step, GeneralBorrowTagMap.Fresh after.tagMapping (reserve step)
  capacity : after.nodes.size = before.nodes.size
  roots : after.roots = before.roots

private theorem fresh_remove (mapping : UniKeyMap BorTag) (removed reserved : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh mapping reserved) :
    GeneralBorrowTagMap.Fresh (mapping.remove removed) reserved := by
  unfold UniKeyMap.remove
  split
  · exact fresh
  · intro row member
    exact fresh row (Array.mem_filter.mp member).1

/-- The actual removal primitive keeps capacity/roots and every unused tag. -/
theorem remove_preserves {n : Nat} (reserve : Fin n → BorTag) (before tree : BorrowTree)
    (index : UniIndex) (good : Frame reserve before tree) :
    Frame reserve before (source_remove_useless_node tree index).1 := by
  cases stored : tree.nodes.get index with
  | none =>
    unfold_source_remove_useless_node
    simpa only [stored,Id.run,bind,pure] using good
  | some node =>
    unfold_source_remove_useless_node
    simp only [stored,Id.run,bind,pure]
    exact ⟨fun step => fresh_remove tree.tagMapping node.tag (reserve step) (good.fresh step),
      (GeneralBorrowSparseRemoval.remove_size tree.nodes index).trans good.capacity,good.roots⟩

theorem update_preserves {n : Nat} (reserve : Fin n → BorTag) (before tree : BorrowTree)
    (index : UniIndex) (oldNode newNode : TreeNode) (present : tree.nodes.get index = some oldNode)
    (good : Frame reserve before tree) : Frame reserve before {tree with nodes := tree.nodes.insert index newNode} :=
  ⟨good.fresh,(GeneralBorrowNodeUpdate.insert_existing_size tree.nodes index oldNode newNode present).trans good.capacity,good.roots⟩

/-- Exact production GC retains caller reservations, capacity and roots,
including partial error states. No successful-operation premise is supplied. -/
theorem preserves {n : Nat} (reserve : Fin n → BorTag) (tree : BorrowTree) (live : Array BorTag)
    (fresh : ∀ step, GeneralBorrowTagMap.Fresh tree.tagMapping (reserve step)) :
    Frame reserve tree (tree.removeUnreachableTags live).tree := by
  apply GeneralBorrowGcRootInvariant.preserves (Frame reserve tree) tree live ⟨fresh,rfl,rfl⟩
  · intro current root initial
    exact GeneralBorrowGcWhileInvariant.preserves (Frame reserve tree)
      (fun current index initial => remove_preserves reserve tree current index initial)
      (fun current index oldNode newNode present _ initial =>
        update_preserves reserve tree current index oldNode newNode present initial)
      current root live initial
  · intro current initial
    exact ⟨initial.fresh,initial.capacity,initial.roots⟩

end DuplicatePrefix.GeneralBorrowGcResourceFrame
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowGcResourceFrame.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved GC resource frame dependency {dependency}"
