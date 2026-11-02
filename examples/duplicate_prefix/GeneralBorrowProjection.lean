import duplicate_prefix.BorrowRangeAccess
import duplicate_prefix.GeneralBorrowTraversal
import duplicate_prefix.GeneralBorrowExposure
namespace DuplicatePrefix.GeneralBorrowProjection
open Miri.ABI Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess
open Lean Elab Tactic
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
elab "unfold_general_projection" : tactic => do
  let candidates := (← getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".BorrowTree.normalProjection" then some name else none
  match candidates with
  | [name] => let name := mkIdent name; evalTactic (← `(tactic| unfold $name:ident))
  | _ => throwError "expected actual normal projection"

elab "unfold_general_topology" : tactic => do
  let candidates := (← getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".BorrowTree.traversalProjection" then some name else none
  match candidates with
  | [name] => let name := mkIdent name; evalTactic (← `(tactic| unfold $name:ident))
  | _ => throwError "expected actual traversal projection"

theorem index_nat (position : Nat) (fits : position ≤ 4294967295) :
    ∃ index, UniIndex.ofNat? position = some index ∧ index.toNat = position := by
  refine ⟨⟨UInt32.ofNat position⟩,?_,?_⟩
  · simp [UniIndex.ofNat?,fits]
  · simp only [UniIndex.toNat,UInt32.toNat_ofNat']
    omega

theorem array_of_node (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodeAt index = some node) :
    ∃ valid : index.toNat < tree.nodes.data.size, tree.nodes.data[index.toNat] = some node := by
  unfold BorrowTree.nodeAt UniValMap.get at present
  cases entry : tree.nodes.data[index.toNat]? with
  | none => simp [entry] at present
  | some value =>
    have valid : index.toNat < tree.nodes.data.size := Array.getElem?_eq_some_iff.mp entry |>.1
    refine ⟨valid,?_⟩
    have same := (Array.getElem?_eq_getElem valid).symm.trans entry
    have slot : tree.nodes.data[index.toNat] = value := Option.some.inj same
    simpa only [entry,slot] using present

theorem projection_state (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (position : Nat) (index : UniIndex) (node : TreeNode)
    (converted : UniIndex.ofNat? position = some index) (indexEq : index.toNat = position)
    (present : tree.nodeAt index = some node) :
    (source_normal_projection tree location protections).stateAt position =
      some ((location.perms.get index).getD node.defaultLocationState) := by
  obtain ⟨valid,slot⟩ := array_of_node tree index node present
  have positionValid : position < tree.nodes.data.size := by omega
  have positionSlot : tree.nodes.data[position] = some node := by simpa only [indexEq] using slot
  unfold_general_projection
  cases stored : location.perms.get index <;>
    simp [NormalTreeState.stateAt,positionValid,converted,positionSlot,TreeNode.defaultLocationState,stored]
theorem index_self (index : UniIndex) : UniIndex.ofNat? index.toNat = some index := by
  have bound := UInt32.toNat_lt index.idx
  have fits : index.toNat ≤ 4294967295 := by unfold UniIndex.toNat; omega
  change index.idx.toNat ≤ 4294967295 at fits
  cases index
  simpa [UniIndex.ofNat?,UniIndex.toNat,UInt32.ofNat_toNat] using fits

theorem projection_sizes (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).locationStates.size = tree.nodes.data.size ∧
    (source_normal_projection tree location protections).defaultStates.size = tree.nodes.data.size := by
  unfold_general_projection
  simp only [Array.size_mapIdx,Array.size_map,and_self]

theorem projection_location_state (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node) :
    (source_normal_projection tree location protections).stateAt index.toNat = tree.locationStateAt location index := by
  rw [projection_state tree location protections index.toNat index node (index_self index) rfl present]
  simp [BorrowTree.locationStateAt,present]

theorem projection_topology_node (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (position : Nat) (index : UniIndex) (node : TreeNode)
    (indexEq : index.toNat = position) (present : tree.nodeAt index = some node) :
    (source_normal_projection tree location protections).topology.nodes[position]?.getD ⟨none,[]⟩ =
      ⟨node.parent.map UniIndex.toNat,node.children.toList.map UniIndex.toNat⟩ := by
  obtain ⟨valid,slot⟩ := array_of_node tree index node present
  have positionValid : position < tree.nodes.data.size := by omega
  have positionSlot : tree.nodes.data[position] = some node := by simpa only [indexEq] using slot
  unfold_general_projection
  unfold_general_topology
  simp [positionValid,positionSlot]

end DuplicatePrefix.GeneralBorrowProjection

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowProjection." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved general projection dependency {dependency}"
