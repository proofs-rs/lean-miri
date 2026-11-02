import duplicate_prefix.GeneralBorrowTwoProtectedStateInfoConflict
namespace DuplicatePrefix.GeneralBorrowTwoProtectedStateInfoEdges
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- In the actual singleton-root ranked forest, the constructor's root is
parentless and a present node with a root parent is physically listed by that
root. The positive requested range internally supplies a stored forest row. -/
theorem root_edges (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (roots : input.tree.roots = #[input.parent])
    (readable : Every (GeneralBorrowProtectedReadRelease.Profile input.tree protections) input.tree.locations)
    (earlier : UniIndex) (earlierNode : TreeNode) (earlierPresent : input.tree.nodeAt earlier = some earlierNode)
    (edge : earlierNode.parent = some input.parent) :
    input.parentNode.parent = none ∧ earlier ∈ input.parentNode.children := by
  have nonempty : input.tree.locations.entries.size ≠ 0 := by
    intro zero
    have empty := Array.size_eq_zero_iff.mp zero
    have capacity : input.tree.locations.size = Size.ZERO := by
      unfold DedupRangeMap.size
      rw [empty]
      rfl
    have bounds := input.bounds
    rw [capacity] at bounds
    change input.offset.toNat+input.len.toNat ≤ 0 at bounds
    have lengthZero : input.len = 0 := UInt64.toNat_inj.mp (by change input.len.toNat = 0;omega)
    exact input.nonzero lengthZero
  let location := input.tree.locations.entries[0]'(by omega) |>.data
  obtain ⟨⟨forest⟩,data⟩ := readable 0 (by omega)
  let normal := source_normal_projection input.tree location protections
  have rootValid : input.parent.toNat < normal.topology.nodes.size := GeneralBorrowProtectedReadPermissionMetadata.valid_anchor input.tree location protections input.parent input.parentNode input.parentPresent
  have earlierValid : earlier.toNat < normal.topology.nodes.size := GeneralBorrowProtectedReadPermissionMetadata.valid_anchor input.tree location protections earlier earlierNode earlierPresent
  have terminal := GeneralBorrowTerminal.ancestor_terminal normal.topology forest input.parent.toNat rootValid
  have lastRoot := GeneralBorrowTerminal.ancestor_root_present normal.topology forest (GeneralBorrowGraph.Present input.tree)
    (GeneralBorrowGraph.parents_closed input.tree location protections input.depth) input.parent.toNat input.parent.toNat rootValid
    ⟨input.parent,input.parentNode,rfl,input.parentPresent⟩
    (fun index _ present parentless => GeneralBorrowGraph.unique_root input.tree location protections input.parent roots input.covered index present parentless)
  rw [lastRoot] at terminal
  unfold GeneralBorrowPresence.nodeData at terminal
  rw [projection_topology_node input.tree location protections input.parent.toNat input.parent input.parentNode rfl input.parentPresent] at terminal
  have parentless : input.parentNode.parent = none := by
    cases parent : input.parentNode.parent with
    | none => rfl
    | some value => simp only [parent,Option.map_some] at terminal;cases terminal
  have rootShape : normal.topology.nodes[input.parent.toNat] =
      ⟨input.parentNode.parent.map UniIndex.toNat,input.parentNode.children.toList.map UniIndex.toNat⟩ := by
    have shape := projection_topology_node input.tree location protections input.parent.toNat input.parent input.parentNode rfl input.parentPresent
    change normal.topology.nodes[input.parent.toNat]?.getD _ = _ at shape
    simpa only [Array.getElem?_eq_getElem rootValid,Option.getD_some] using shape
  have earlierShape : normal.topology.nodes[earlier.toNat] =
      ⟨earlierNode.parent.map UniIndex.toNat,earlierNode.children.toList.map UniIndex.toNat⟩ := by
    have shape := projection_topology_node input.tree location protections earlier.toNat earlier earlierNode rfl earlierPresent
    change normal.topology.nodes[earlier.toNat]?.getD _ = _ at shape
    simpa only [Array.getElem?_eq_getElem earlierValid,Option.getD_some] using shape
  have childEdge : normal.topology.nodes[earlier.toNat].parent = some input.parent.toNat := by
    rw [earlierShape,edge];rfl
  obtain ⟨_,listed⟩ := forest.parentChild earlier.toNat earlierValid input.parent.toNat childEdge
  rw [rootShape] at listed
  obtain ⟨query,member,equal⟩ := List.mem_map.mp listed
  have same : query = earlier := GeneralBorrowNodeUpdate.index_injective query earlier equal
  subst query
  exact ⟨parentless,Array.mem_def.mpr member⟩
end DuplicatePrefix.GeneralBorrowTwoProtectedStateInfoEdges
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowTwoProtectedStateInfoEdges.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved two protected state edges dependency {dependency}"
