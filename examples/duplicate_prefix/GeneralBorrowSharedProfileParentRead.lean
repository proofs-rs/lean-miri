import duplicate_prefix.GeneralBorrowSharedProfileRead
import duplicate_prefix.GeneralBorrowExposeReadParentRead
namespace DuplicatePrefix.GeneralBorrowSharedProfileParentRead
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowSharedGeneratorProfile
open DuplicatePrefix.GeneralBorrowExposeReadParentRead
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- A parentless source has exactly the singleton local ancestor path. -/
theorem parent_path (input : Input) (location : LocationTree) (protections : ProtectedTags)
    (parentless : input.parentNode.parent = none) :
    (source_normal_projection input.tree location protections).topology.ancestorPath input.parent.toNat = [input.parent.toNat] := by
  have parent : (GeneralBorrowPresence.nodeData (source_normal_projection input.tree location protections).topology input.parent.toNat).parent = none := by
    change ((source_normal_projection input.tree location protections).topology.nodes[input.parent.toNat]?.getD ⟨none,[]⟩).parent = none
    rw [projection_topology_node input.tree location protections input.parent.toNat input.parent input.parentNode rfl input.parentPresent]
    simp only [parentless,Option.map_none]
  change sourceAncestorPath (source_normal_projection input.tree location protections).topology
    (source_normal_projection input.tree location protections).topology.nodes.size input.parent.toNat = _
  cases (source_normal_projection input.tree location protections).topology.nodes.size with
  | zero => rfl
  | succ fuel => rw [GeneralBorrowPresence.ancestor_succ,parent]

/-- A genuine one-byte concrete single-root parent Read completes, retains the
exact generator profile (including sparse vacant Clean), and supplies ownership
for the next Read. Graph, settings and initial profile remain explicit; neither
operation success nor a poststate is an input. This does not yet include append. -/
theorem read_closed (input : Input) (location : LocationTree)
    (offset : input.offset = 0) (length : input.len = 1)
    (initial : input.tree.locations = RangeMapNonempty.homogeneous 1 location)
    (roots : input.tree.roots = #[input.parent])
    (parentless : input.parentNode.parent = none)
    (forest : GeneralBorrowForest.Forest (source_normal_projection input.tree location {}).topology)
    (profile : Profile input.tree location input.parent) :
    (read input {}).status = .Completed ∧
    (read input {}).tree = (afterReadInput input location {} offset length).tree ∧
    Profile (afterReadInput input location {} offset length).tree (readLocation input location {}) input.parent ∧
    GeneralBorrowAnchor.AnchorOwned
      (source_normal_projection (afterReadInput input location {} offset length).tree (readLocation input location {}) {})
      input.parent.toNat .Read := by
  have owned := read_owned input location parentless profile
  have facts := read_exact input location {} initial roots forest owned
  have valid := owned.anchorValid
  have preserved := GeneralBorrowSharedProfileRead.normal input location {} .VisitChildrenOfAccessed profile
    (by
      intro event member
      have classified := (GeneralBorrowTraversal.traversal_data _ forest input.parent.toNat valid
        .VisitChildrenOfAccessed (sourceNormalSkipped (source_normal_projection input.tree location {}) .Read)).2 event member
      simpa only [parent_path input location {} parentless,List.mem_singleton] using classified.2)
  have nextProfile : Profile (afterReadInput input location {} offset length).tree
      (readLocation input location {}) input.parent :=
    ⟨preserved.rootStored,preserved.shared,preserved.vacant⟩
  exact ⟨facts.1,facts.2,nextProfile,
    read_owned (afterReadInput input location {} offset length) (readLocation input location {}) parentless nextProfile⟩
end DuplicatePrefix.GeneralBorrowSharedProfileParentRead
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowSharedProfileParentRead.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared parent Read profile dependency {dependency}"
