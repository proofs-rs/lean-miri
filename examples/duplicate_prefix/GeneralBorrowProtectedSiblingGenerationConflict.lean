import duplicate_prefix.GeneralBorrowTwoProtectedStateInfoConflict
import duplicate_prefix.GeneralBorrowProtectedReadStable
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationConflict
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState GeneralRangeMapOrigins GeneralBorrowProjection BorrowRangeAccess
open GeneralBorrowConstructorPriorPermission
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- An earlier established reservation conflict is retained by an actual later
constructor-leading Read. Neither visitation nor skip success is supplied. -/
theorem read (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (roots : input.tree.roots = #[input.parent])
    (readable : Every (GeneralBorrowProtectedReadRelease.Profile input.tree protections) input.tree.locations)
    (query : UniIndex) (node : TreeNode) (present : input.tree.nodeAt query = some node)
    (default : node.defaultInitialPermission = .ReservedFrz false)
    (initial : Every (At query (some (.ReservedFrz true))) input.tree.locations) :
    OwnedOn (At query (some (.ReservedFrz true))) input.offset (input.offset+input.len)
      (GeneralBorrowProtectedReadableStage.read input protections).tree.locations := by
  apply GeneralBorrowRangeCallbackOutput.outputs input.tree protections input.parentTag input.parent
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read .VisitChildrenOfAccessed (At query (some (.ReservedFrz true)))
    input.parentTagPresent input.well input.bounds
  intro cursor valid
  have prepared := GeneralRangeMapSafety.iter_mut
    (fun location => GeneralBorrowProtectedReadRelease.Profile input.tree protections location ∧ At query (some (.ReservedFrz true)) location)
    input.tree.locations (Size.ofBytes input.offset) (Size.ofBytes input.len) input.well
    (fun position valid => ⟨readable position valid,initial position valid⟩) input.bounds
  have cursorBound : cursor < (input.tree.locations.iterMut (Size.ofBytes input.offset) (Size.ofBytes input.len)).positions.size := by rw [prepared.lengths];exact valid
  obtain ⟨positionBound,selected⟩ := prepared.selected cursor cursorBound
  let segment := (input.tree.locations.iterMut (Size.ofBytes input.offset) (Size.ofBytes input.len)).segments[cursor]
  have data : GeneralBorrowProtectedReadRelease.Profile input.tree protections segment.data ∧ At query (some (.ReservedFrz true)) segment.data := by
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
  have before : ((segment.data.perms.get query).getD node.defaultLocationState).permission = .ReservedFrz true := by
    have storedAt := data.2
    cases stored : segment.data.perms.get query with
    | none => simp only [At,stored,Option.map_none] at storedAt;cases storedAt
    | some state => simpa only [At,stored,Option.map_some,Option.some.injEq,Option.getD_some] using storedAt
  have kept := GeneralBorrowProtectedReadStable.normal_permission input.tree segment.data protections input.parent .VisitChildrenOfAccessed
    input.depth input.children input.parentNode input.parentPresent forest profile query node present (Or.inl before)
  unfold At
  cases stored : (input.tree.performNormalAccessAt segment.data input.parent .Read protections .VisitChildrenOfAccessed).location.perms.get query with
  | none => rw [before] at kept
            simp only [stored,Option.getD_none,TreeNode.defaultLocationState,default] at kept
            cases kept
  | some state => simpa only [stored,Option.getD_some,before,Option.map_some] using congrArg some kept

theorem child (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (roots : input.tree.roots = #[input.parent])
    (readable : Every (GeneralBorrowProtectedReadRelease.Profile input.tree protections) input.tree.locations)
    (prepared : GeneralBorrowProtectedReadableStage.Prepared input protections)
    (query : UniIndex) (node : TreeNode) (present : input.tree.nodeAt query = some node)
    (default : node.defaultInitialPermission = .ReservedFrz false)
    (initial : Every (At query (some (.ReservedFrz true))) input.tree.locations) :
    OwnedOn (At query (some (.ReservedFrz true))) input.offset (input.offset+input.len)
      (GeneralBorrowProtectedReadableStage.child input protections).tree.locations := by
  have readResult := read input protections roots readable query node present default initial
  have frame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read protections .VisitChildrenOfAccessed
  change (GeneralBorrowProtectedReadableStage.read input protections).tree =
    {input.tree with locations := (GeneralBorrowProtectedReadableStage.read input protections).tree.locations} at frame
  have mapping : prepared.next.tree.tagMapping = input.tree.tagMapping := by rw [prepared.tree,frame]
  have different : query ≠ GeneralBorrowFreshMetadataChildMutable.index prepared.next := by
    intro same
    have bound := (array_of_node input.tree query node present).1
    have index : GeneralBorrowFreshMetadataChildMutable.index prepared.next = GeneralBorrowFreshMetadataChildMutable.index input := by
      unfold GeneralBorrowFreshMetadataChildMutable.index
      rw [mapping]
    have equal := congrArg UniIndex.toNat (same.trans index)
    rw [GeneralBorrowFreshMetadataChildMutable.at_end input] at equal
    omega
  have owned : OwnedOn (At query (some (.ReservedFrz true))) input.offset (input.offset+input.len) prepared.next.tree.locations := by rw [prepared.tree];exact readResult
  have result := GeneralBorrowConstructorPriorPermissionRange.protected_append prepared.next query (some (.ReservedFrz true))
    input.offset (input.offset+input.len) different owned
  rw [prepared.result] at result
  exact result.2
end DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationConflict
