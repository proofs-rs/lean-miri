import duplicate_prefix.CurrentCallEmptyEntryBool

namespace DuplicatePrefix.CurrentCallEmptyEntryFactoryLocations
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CurrentCallEmptyEntryBool
open GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

private theorem path (tree : BorrowTree) (locations : DedupRangeMap LocationTree) (root query : UniIndex) :
    Path {tree with locations:=locations} root query ↔ Path tree root query := by
  constructor <;> intro actual
  · apply GeneralBorrowSharedAuthorizationGeometry.path_extension {tree with locations:=locations} tree _ root query actual
    intro index node present
    exact ⟨node,present,rfl⟩
  · apply GeneralBorrowSharedAuthorizationGeometry.path_extension tree {tree with locations:=locations} _ root query actual
    intro index node present
    exact ⟨node,present,rfl⟩

/-- Runtime row updates retain the SAME actual constructor geometry. -/
theorem transport (tree : BorrowTree) (C : Completion) (flags : ProtectedTags) (source : UniIndex) (qTag : BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (locations : DedupRangeMap LocationTree)
    (factory : OrphanWriteFactory tree C flags source qTag) :
    Nonempty (OrphanWriteFactory {tree with locations:=locations} C flags source qTag) := by
  refine ⟨⟨factory.selectedPosition,factory.selected,factory.selectedNode,factory.selectedSlot,factory.selectedAt,
    (path tree locations _ _).mpr factory.selectedPath,factory.orphan,factory.orphanPosition,factory.orphanMapped,
    factory.orphanSlot,factory.later,factory.notBelow,factory.different,factory.distinct,?_,?_⟩⟩
  · intro query node present included
    have old := factory.selectedClassification query node present ((path tree locations _ _).mp included)
    exact old.trans (path tree locations query source).symm
  · intro current authority position root rootSlot different consistent
    have beforeAuthority : S05CompletedAncestryReadMutable.Authority tree C flags source current := by
      intro query node present
      exact authority query node present
    obtain ⟨queries⟩ := factory.callbacks current beforeAuthority position root rootSlot different (by
      intro query node present included
      exact consistent query node present ((path tree locations _ _).mpr included))
    obtain ⟨authorization,classification⟩ := CurrentCallEmptyEntryRepairedMetadata.queries tree {tree with locations:=locations}
      current current flags depth depth (Nat.le_refl _)
      (by intro index node present;exact ⟨node,present,rfl,rfl,rfl,rfl⟩)
      (by intro index node present _;exact ⟨node,present⟩) root position (some factory.selectedNode.tag) .Write queries.support
      queries.authorization (by intro;intro;rfl) (by intro;intro;rfl) C C source queries.classification
      (by intro;intro;exact Iff.rfl)
    exact ⟨⟨queries.support,authorization,(fun query included => (path tree locations _ _).mpr (queries.path query included)),classification⟩⟩
end
end DuplicatePrefix.CurrentCallEmptyEntryFactoryLocations

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryFactoryLocations" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved empty factory row transport dependency {dependency}"
