import duplicate_prefix.GeneralBorrowProtectedConstructorReadable
import duplicate_prefix.GeneralBorrowFreshMutableGeometry
import duplicate_prefix.GeneralBorrowFreshFutureClean
import duplicate_prefix.GeneralBorrowProtectedDefaultInvariant
namespace DuplicatePrefix.GeneralBorrowProtectedNextInput
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshMetadataChildMutable
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Construct the next real same-root protected append Input from the actual
previous protected append. The caller supplies only future tag/room resources;
parent metadata, allocator facts and geometry are internally derived. -/
noncomputable def after (input : Input) (future : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh input.tree.tagMapping future) (different : input.newTag ≠ future)
    (room : input.tree.tagMapping.mapping.size+1 ≤ 4294967295) : Input := by
  let output := append input
  have parentPresent : (stage input).nodeAt input.parent =
      some (GeneralBorrowFreshGraph.updatedParent input.parentNode (index input)) := by
    exact GeneralBorrowFreshGraph.parent_lookup input.tree (index input) input.parent input.parentNode
      (GeneralBorrowFreshChild.child input.newTag input.parent) (at_end input) input.parentPresent
  let facts := GeneralBorrowFreshMetadata.node_fields (stage input) (result input) (shape input) input.parent _ parentPresent
  let node := Classical.choose facts
  have present := (Classical.choose_spec facts).1
  have distinct : input.newTag ≠ input.parentTag := by
    intro equal
    have absent : input.tree.indexOfTag input.newTag = none := by
      simp only [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find input.tree.tagMapping input.newTag input.fresh,Option.map_none]
    have lookup : input.tree.indexOfTag input.parentTag = some input.parent := input.parentTagPresent
    rw [equal,lookup] at absent
    cases absent
  have geometry := GeneralBorrowFreshMutableGeometry.append_frame input
  exact {
    tree := result input
    depth := output.certificates.depth
    children := output.certificates.children
    covered := output.certificates.covered
    parentTag := input.parentTag
    newTag := future
    parent := input.parent
    parentNode := node
    parentTagPresent := (output.oldLookup input.parentTag distinct).trans input.parentTagPresent
    parentPresent := present
    fresh := by
      intro row member
      rw [output.mapping] at member
      simp only [mapping,Array.mem_push] at member
      rcases member with old | equal
      · exact fresh row old
      · subst row;exact different
    noFree := output.noFree
    aligned := output.aligned
    fits := by rw [output.mapping];simpa only [mapping,Array.size_push] using room
    offset := input.offset
    len := input.len
    nonzero := input.nonzero
    well := geometry.1
    bounds := by rw [geometry.2];exact input.bounds }

/-- Exposure and other actual permission/topology-shape frames retain the raw
metadata required by the next protected append; its parent node is re-formed. -/
noncomputable def shape_input (input : Input) (after : BorrowTree)
    (same : GeneralBorrowView.treeShape after = GeneralBorrowView.treeShape input.tree) : Input := by
  let facts := GeneralBorrowFreshMetadata.node_fields input.tree after same input.parent input.parentNode input.parentPresent
  let node := Classical.choose facts
  have present := (Classical.choose_spec facts).1
  have mapping : after.tagMapping = input.tree.tagMapping := congrArg Prod.fst same
  have sizes : after.nodes.data.size = input.tree.nodes.data.size := by
    have rows := congrArg (fun row => row.2.1) same
    simpa only [GeneralBorrowView.treeShape,Array.size_map] using congrArg Array.size rows
  have geometry := GeneralBorrowFreshGeometry.shape_frame input.tree after same input.well
  exact {
    input with
    tree := after
    depth := GeneralBorrowFreshMetadata.parent_depth input.tree after same input.depth
    children := GeneralBorrowFreshMetadata.child_nodes input.tree after same input.children
    covered := GeneralBorrowFreshMetadata.roots_cover input.tree after same input.covered
    parentNode := node
    parentTagPresent := by change after.tagMapping.get input.parentTag = _;rw [mapping];exact input.parentTagPresent
    parentPresent := present
    fresh := by rw [mapping];exact input.fresh
    noFree := by rw [mapping];exact input.noFree
    aligned := by rw [mapping,sizes];exact input.aligned
    fits := by rw [mapping];exact input.fits
    well := geometry.1
    bounds := by rw [geometry.2];exact input.bounds }

/-- Installing the current child and its real ancestor SIFA does not consume
any other initial future Clean permission slot. -/
theorem future_clean (input : Input) (query : UniIndex) (different : query ≠ index input)
    (clean : GeneralBorrowFreshFutureClean.Clean input.tree query) :
    GeneralBorrowFreshFutureClean.Clean (result input) query := by
  have modified := GeneralBorrowFreshFutureClean.modified input.tree.locations (index input) query
    (Size.ofBytes input.offset) (Size.ofBytes input.len) GeneralBorrowFreshChild.inside different input.well input.bounds clean
  apply GeneralBorrowFreshFutureClean.shape_preserves (stage input) (result input) (shape input) query
  exact modified
end DuplicatePrefix.GeneralBorrowProtectedNextInput
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedNextInput.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected next Input dependency {dependency}"
