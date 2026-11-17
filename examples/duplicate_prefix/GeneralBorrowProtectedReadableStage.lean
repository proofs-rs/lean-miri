import duplicate_prefix.GeneralBorrowProtectedConstructorReadable
import duplicate_prefix.GeneralBorrowProtectedReadRangeClean
import duplicate_prefix.GeneralBorrowProtectedReadRange
import duplicate_prefix.GeneralBorrowFreshReadFrame
namespace DuplicatePrefix.GeneralBorrowProtectedReadableStage
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralBorrowProtectedReadRelease (Profile)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def read (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags) :=
  input.tree.performNormalAccessRange input.parentTag (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read protections .VisitChildrenOfAccessed

def child (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags) :=
  (read input protections).tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
    (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true

/-- Internally derived source Read→constructor input, retained for allocator
and parent-node formation of a later fresh protected constructor. -/
structure Prepared (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags) where
  next : GeneralBorrowFreshMetadataChildMutable.Input
  tree : next.tree = (read input protections).tree
  tag : next.newTag = input.newTag
  parentTag : next.parentTag = input.parentTag
  parent : next.parent = input.parent
  parentNode : next.parentNode = input.parentNode
  offset : next.offset = input.offset
  len : next.len = input.len
  result : GeneralBorrowFreshMetadataChildMutable.result next = (child input protections).tree
  completed : (read input protections).status = .Completed
  success : (child input protections).outcome = .ok ()
  profile : Every (Profile (child input protections).tree protections) (child input protections).tree.locations

/-- Real bounded Read and real protected Default append preserve the readable
forest profile needed for simultaneously held lifetimes and their release scans.
Both operation successes and the next constructor Input are derived internally. -/
def prepare (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (roots : input.tree.roots = #[input.parent])
    (initial : Every (Profile input.tree protections) input.tree.locations)
    (clean : Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildMutable.index input) = none) input.tree.locations) :
    Prepared input protections := by
  have fits : input.tree.nodes.data.size ≤ 4294967296 := by
    have bound := input.fits
    have aligned := input.aligned
    omega
  have accessed := GeneralBorrowProtectedReadRangeClean.preserves input.tree protections input.parentTag input.parent input.parent
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .VisitChildrenOfAccessed
    (GeneralBorrowFreshMetadataChildMutable.index input) (by rw [GeneralBorrowFreshMetadataChildMutable.at_end input];exact Nat.le_refl _) clean fits
    input.depth input.children input.parentNode input.parentPresent roots input.covered input.parentTagPresent input.well initial input.bounds
  have compatible : Every (GeneralBorrowProtectedReadRange.LocationCompatible input.tree protections input.parent) input.tree.locations := by
    intro position valid
    obtain ⟨forest,data⟩ := initial position valid
    refine ⟨forest,?_,?_⟩
    · obtain ⟨bounded,_⟩ := GeneralBorrowProjection.array_of_node input.tree input.parent input.parentNode input.parentPresent
      unfold_general_projection;unfold_general_topology;simpa only [Array.size_map] using bounded
    · intro index bounded
      have aligned : (source_normal_projection input.tree input.tree.locations.entries[position].data protections).locationStates.size =
          (source_normal_projection input.tree input.tree.locations.entries[position].data protections).topology.nodes.size := by
        unfold_general_projection;unfold_general_topology;simp only [Array.size_mapIdx,Array.size_map]
      obtain ⟨state,present,good⟩ := data index (by omega)
      exact ⟨state,present,GeneralBorrowProtectedReadInvariant.compatible state _ _ good⟩
  have geometry := GeneralBorrowProtectedReadRange.geometry input.tree protections input.parentTag input.parent input.parent
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .VisitChildrenOfAccessed input.depth input.children input.parentNode
    input.parentPresent roots input.covered input.parentTagPresent input.well compatible input.bounds
  change (read input protections).tree.locations.WellFormed ∧ (read input protections).tree.locations.size = input.tree.locations.size at geometry
  have frame : (read input protections).tree = {input.tree with locations := (read input protections).tree.locations} :=
    GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
      .Read protections .VisitChildrenOfAccessed
  have nodes : (read input protections).tree.nodes = input.tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have mapping : (read input protections).tree.tagMapping = input.tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
  let next : GeneralBorrowFreshMetadataChildMutable.Input := {
    input with
    tree := (read input protections).tree
    depth := GeneralBorrowFreshReadFrame.depth_on input.tree _ nodes input.depth
    children := by rw [frame];exact input.children
    covered := by rw [frame];exact input.covered
    parentTagPresent := by rw [frame];exact input.parentTagPresent
    parentPresent := by rw [frame];exact input.parentPresent
    fresh := by rw [frame];exact input.fresh
    noFree := by rw [frame];exact input.noFree
    aligned := by rw [frame];exact input.aligned
    fits := by rw [frame];exact input.fits
    well := geometry.1
    bounds := by rw [geometry.2];exact input.bounds }
  have index : GeneralBorrowFreshMetadataChildMutable.index next = GeneralBorrowFreshMetadataChildMutable.index input := by
    change (⟨UInt32.ofNat (read input protections).tree.tagMapping.mapping.size⟩ : UniIndex) = _
    rw [mapping]
    rfl
  have afterProfile : Every (Profile next.tree protections) next.tree.locations := fun position valid => (accessed.2 position valid).1
  have afterClean : Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildMutable.index next) = none) next.tree.locations := by
    intro position valid
    rw [index]
    exact (accessed.2 position valid).2
  have recurring := GeneralBorrowProtectedConstructorReadable.append next protections afterProfile afterClean
  exact ⟨next,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,accessed.1,(GeneralBorrowFreshMetadataChildMutable.append next).success,recurring⟩
end DuplicatePrefix.GeneralBorrowProtectedReadableStage
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedReadableStage.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected readable stage dependency {dependency}"
