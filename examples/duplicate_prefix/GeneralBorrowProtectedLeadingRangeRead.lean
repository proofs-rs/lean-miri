import duplicate_prefix.GeneralBorrowProtectedChildReadSchedule
import duplicate_prefix.GeneralBorrowRangeCallbackOutput
import duplicate_prefix.GeneralBorrowRangeLocal
import duplicate_prefix.GeneralBorrowConstructorPriorPermissionRange
namespace DuplicatePrefix.GeneralBorrowProtectedLeadingRangeRead
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralRangeMapOrigins
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowConstructorPriorPermission
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Initial one-location facts for an earlier held reservation on the later
constructor's window. No intermediate read success is supplied. -/
def Before (tree : BorrowTree) (protections : ProtectedTags) (root earlier : UniIndex) (location : LocationTree) : Prop :=
  GeneralBorrowRange.LocationOwned tree protections root .Read location ∧
  GeneralBorrowLocationSifaConsistency.Profile tree location protections ∧
  ∃ state,tree.locationStateAt location earlier = some state ∧ state.permission = .ReservedFrz false

/-- The pinned typed retag paths use VisitChildrenOfAccessed for their leading
Read (RetagPipeline.lean228-230; RetagPipelineEffectful.lean102-104).
Actual range preparation and writeback conflict the earlier direct child's
reservation throughout the later constructor's bounded window. -/
theorem read (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (root earlier : UniIndex)
    (rootNode earlierNode : TreeNode) (offset len : UInt64)
    (fits : tree.nodes.data.size ≤ 4294967296) (depth : ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (covered : GeneralBorrowGraph.RootsCover tree)
    (roots : tree.roots = #[root]) (tagPresent : tree.indexOfTag tag = some root)
    (rootPresent : tree.nodeAt root = some rootNode) (parentless : rootNode.parent = none)
    (earlierPresent : tree.nodeAt earlier = some earlierNode) (listed : earlier ∈ rootNode.children)
    (held : protections.contains earlierNode.tag = true) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (initial : OwnedOn (Before tree protections root earlier) offset (offset+len) tree.locations) :
    let result := tree.performNormalAccessRange tag (Size.ofBytes offset) (Size.ofBytes len) .Read protections .VisitChildrenOfAccessed
    result.status = .Completed ∧
      OwnedOn (At earlier (some (.ReservedFrz true))) offset (offset+len) result.tree.locations := by
  have sourceOwned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections root .Read) offset (offset+len) tree.locations := by
    intro position valid positive beforeUpper afterLower
    exact (initial position valid positive beforeUpper afterLower).1
  have complete := GeneralBorrowRangeLocal.access tree protections tag root root (Size.ofBytes offset) (Size.ofBytes len)
    .Read .Read .VisitChildrenOfAccessed (fun _ => rfl) fits depth children rootNode rootPresent roots covered
    tagPresent well offset (offset+len) sourceOwned bounds (Nat.le_refl _) (Nat.le_refl _)
  refine ⟨complete.1,?_⟩
  apply GeneralBorrowRangeCallbackOutput.outputs tree protections tag root (Size.ofBytes offset) (Size.ofBytes len)
    .Read .VisitChildrenOfAccessed (At earlier (some (.ReservedFrz true))) tagPresent well bounds
  intro cursor valid
  have selected := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations (Size.ofBytes offset) (Size.ofBytes len)
    well bounds (Before tree protections root earlier) offset (offset+len) initial (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨⟨⟨forest⟩,owner⟩,profile,state,stored,reservation⟩ := selected.2.2 cursor valid
  let segment := (tree.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)).segments[cursor]
  have conflict := GeneralBorrowProtectedChildReadSchedule.root_read tree segment.data protections root earlier rootNode earlierNode state
    fits depth children rootPresent parentless earlierPresent listed stored reservation held forest owner profile
  have actual := GeneralBorrowSingleRoot.access_at tree segment.data protections root root .Read .VisitChildrenOfAccessed segment.range
    forest owner depth children rootNode rootPresent roots covered
  refine ⟨actual,?_⟩
  rw [GeneralBorrowRangePreserves.single_root_location tree segment.data protections root root .Read .VisitChildrenOfAccessed segment.range
    forest owner depth children rootNode rootPresent roots covered]
  obtain ⟨next,present,permission⟩ := conflict.2.2
  simp only [At,present,Option.map_some,permission]

end DuplicatePrefix.GeneralBorrowProtectedLeadingRangeRead
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedLeadingRangeRead.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected leading range Read dependency {dependency}"
