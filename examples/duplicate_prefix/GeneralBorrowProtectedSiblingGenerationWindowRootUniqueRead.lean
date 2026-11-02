import duplicate_prefix.GeneralBorrowTwoProtectedStateInfoConflict
import duplicate_prefix.GeneralBorrowReadUnique
import duplicate_prefix.GeneralBorrowWriteActivationUnique
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindowRootUniqueRead
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState GeneralRangeMapOrigins GeneralBorrowProjection BorrowRangeAccess
open GeneralBorrowConstructorPriorPermission
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The actual constructor-leading Read retains its parent's stored Unique
permission. Traversal relatedness is derived from the source forest. -/
theorem read (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (roots : input.tree.roots = #[input.parent])
    (readable : Every (GeneralBorrowProtectedReadRelease.Profile input.tree protections) input.tree.locations)
    (initial : Every (At input.parent (some .Unique)) input.tree.locations) :
    OwnedOn (At input.parent (some .Unique)) input.offset (input.offset+input.len)
      (GeneralBorrowProtectedReadableStage.read input protections).tree.locations := by
  apply GeneralBorrowRangeCallbackOutput.outputs input.tree protections input.parentTag input.parent
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read .VisitChildrenOfAccessed (At input.parent (some .Unique))
    input.parentTagPresent input.well input.bounds
  intro cursor valid
  have prepared := GeneralRangeMapSafety.iter_mut
    (fun location => GeneralBorrowProtectedReadRelease.Profile input.tree protections location ∧ At input.parent (some .Unique) location)
    input.tree.locations (Size.ofBytes input.offset) (Size.ofBytes input.len) input.well
    (fun position valid => ⟨readable position valid,initial position valid⟩) input.bounds
  have cursorBound : cursor < (input.tree.locations.iterMut (Size.ofBytes input.offset) (Size.ofBytes input.len)).positions.size := by rw [prepared.lengths];exact valid
  obtain ⟨positionBound,selected⟩ := prepared.selected cursor cursorBound
  let segment := (input.tree.locations.iterMut (Size.ofBytes input.offset) (Size.ofBytes input.len)).segments[cursor]
  have data : GeneralBorrowProtectedReadRelease.Profile input.tree protections segment.data ∧ At input.parent (some .Unique) segment.data := by
    dsimp only [segment]
    rw [selected];exact prepared.every _ positionBound
  obtain ⟨⟨forest⟩,profile⟩ := data.1
  have validRoot := GeneralBorrowProtectedReadPermissionMetadata.valid_anchor input.tree segment.data protections input.parent input.parentNode input.parentPresent
  have compatible := GeneralBorrowProtectedReadPermissionMetadata.compatible_initial input.tree segment.data protections input.parent profile
  have actual := GeneralBorrowProtectedReadSingleRoot.access_at input.tree segment.data protections input.parent input.parent .VisitChildrenOfAccessed segment.range
    forest validRoot compatible input.depth input.children input.parentNode input.parentPresent roots input.covered
  refine ⟨actual,?_⟩
  rw [GeneralBorrowProtectedReadSingleRoot.single_root_location input.tree segment.data protections input.parent input.parent .VisitChildrenOfAccessed segment.range
    forest validRoot compatible input.depth input.children input.parentNode input.parentPresent roots input.covered]
  have old : ∃ state,segment.data.perms.get input.parent = some state ∧ state.permission = .Unique := by
    have storedAt := data.2
    cases stored : segment.data.perms.get input.parent with
    | none => simp only [At,stored,Option.map_none] at storedAt;cases storedAt
    | some state => exact ⟨state,rfl,by simpa only [At,stored,Option.map_some,Option.some.injEq] using storedAt⟩
  have kept := GeneralBorrowReadUnique.normal_unique input.tree segment.data protections input.parent input.parent input.parentNode
    .VisitChildrenOfAccessed input.parentPresent old (by
      let normal := source_normal_projection input.tree segment.data protections
      have schedule := GeneralBorrowTraversal.traversal_data normal.topology forest input.parent.toNat validRoot
        .VisitChildrenOfAccessed (sourceNormalSkipped normal .Read)
      have selfPath : input.parent.toNat ∈ normal.topology.ancestorPath input.parent.toNat := by
        change input.parent.toNat ∈ sourceAncestorPath normal.topology normal.topology.nodes.size input.parent.toNat
        cases normal.topology.nodes.size with
        | zero => simp only [GeneralBorrowPresence.ancestor_zero,List.mem_singleton]
        | succ fuel => rw [GeneralBorrowPresence.ancestor_succ];split <;> simp
      intro event member same
      have related := (schedule.2 event member).2
      rw [related,same]
      simp only [selfPath,↓reduceIte])
  obtain ⟨state,stored,permission⟩ := kept
  simp only [At,stored,Option.map_some,permission]

theorem child (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (roots : input.tree.roots = #[input.parent])
    (readable : Every (GeneralBorrowProtectedReadRelease.Profile input.tree protections) input.tree.locations)
    (prepared : GeneralBorrowProtectedReadableStage.Prepared input protections)
    (initial : Every (At input.parent (some .Unique)) input.tree.locations) :
    OwnedOn (At input.parent (some .Unique)) input.offset (input.offset+input.len)
      (GeneralBorrowProtectedReadableStage.child input protections).tree.locations := by
  have readResult := read input protections roots readable initial
  have frame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read protections .VisitChildrenOfAccessed
  change (GeneralBorrowProtectedReadableStage.read input protections).tree =
    {input.tree with locations := (GeneralBorrowProtectedReadableStage.read input protections).tree.locations} at frame
  have mapping : prepared.next.tree.tagMapping = input.tree.tagMapping := by rw [prepared.tree,frame]
  have different : input.parent ≠ GeneralBorrowFreshMetadataChildMutable.index prepared.next := by
    intro same
    have bound := (array_of_node input.tree input.parent input.parentNode input.parentPresent).1
    have index : GeneralBorrowFreshMetadataChildMutable.index prepared.next = GeneralBorrowFreshMetadataChildMutable.index input := by
      unfold GeneralBorrowFreshMetadataChildMutable.index
      rw [mapping]
    have equal := congrArg UniIndex.toNat (same.trans index)
    rw [GeneralBorrowFreshMetadataChildMutable.at_end input] at equal
    omega
  have owned : OwnedOn (At input.parent (some .Unique)) input.offset (input.offset+input.len) prepared.next.tree.locations := by rw [prepared.tree];exact readResult
  have result := GeneralBorrowConstructorPriorPermissionRange.protected_append prepared.next input.parent (some .Unique)
    input.offset (input.offset+input.len) different owned
  rw [prepared.result] at result
  exact result.2
end DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindowRootUniqueRead
