import duplicate_prefix.GeneralBorrowConcreteRangeEntry
import duplicate_prefix.S05CompletedAncestryConcreteRead

/-! Actual ranged concrete Read with a Read-only physical reader and separate
other-root mutable-ancestry authority. Saved initial segment data supplies the
input; the actual visitor preserves the other-root scalar tables. -/
namespace DuplicatePrefix.S05CompletedAncestryRangeRead
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality GeneralBorrowProjection
open GeneralRangeMapOrigins GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

theorem access (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
    (complete : Completes tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source reader : UniIndex) (selectedNode readerNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePath : Path tree selected source)
    (readerPresent : tree.nodes.get reader = some readerNode) (readerPath : Path tree selected reader)
    (offset len : Size) (lower upper : UInt64)
    (owned : OwnedOn (fun location => GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
      (∀ index node, tree.nodes.get index = some node → Path tree selected index →
        DuplicatePrefixScalarAuthorization.Compatible ((location.perms.get index).getD node.defaultLocationState) .Read
          (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) reader.toNat index.toNat)
          (protections.contains node.tag)) ∧
      (∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
        ∀ index node, tree.nodes.get index = some node → Path tree root index →
          (Below completion index source → LocalWrite
            ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) ∧
          (¬Below completion index source → ForeignWrite
            ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))))
      lower upper tree.locations)
    (well : tree.locations.WellFormed)
    (runtime : Every (fun location => LocationCoherent tree location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree location protections) tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : lower.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes + len.bytes).toNat ≤ upper.toNat)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) :
    GeneralBorrowConcreteRangeInvariant.Contract tree
      (fun location => GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
        ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
          ∀ index node, tree.nodes.get index = some node → Path tree root index →
            (Below completion index source → LocalWrite
              ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) ∧
            (¬Below completion index source → ForeignWrite
              ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)))
      (fun location => LocationCoherent tree location protections ∧
        GeneralBorrowLocationSifaConsistency.Profile tree location protections)
      (fun before after => before = after ∨
        ∀ index node, tree.nodes.get index = some node → Path tree selected index →
          after.perms.get index =
            (tree.performNormalAccessAt before reader .Read protections mode).location.perms.get index)
      lower upper (tree.performBorrowAccessRange (.concrete readerNode.tag) offset len .Read protections mode) := by
  have mapped : tree.indexOfTag readerNode.tag = some reader :=
    (complete.2.2.2.2.1 reader readerNode readerPresent).1
  apply GeneralBorrowConcreteRangeEntry.access tree protections readerNode.tag reader mapped offset len .Read mode
    _ _ _ _ (fun _ initial => ⟨initial.1,initial.2.2⟩) (fun _ => Or.inl rfl) _
    lower upper owned well runtime bounds requestLower requestUpper
  intro location authority representation range
  have row := S05CompletedAncestryConcreteRead.access tree completion location protections complete formed depth order
    selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath reader readerPath authority.2.1
    (fun position root slot different index node present path below =>
      (authority.2.2 position root slot different index node present path).1 below)
    (fun position root slot different index node present path outside =>
      (authority.2.2 position root slot different index node present path).2 outside)
    representation.1 representation.2 authority.1 short mode range
  refine ⟨row.1,⟨row.2.2.2.1,?_⟩,⟨row.2.1,row.2.2.1⟩,Or.inr row.2.2.2.2.1⟩
  intro position root slot different index node present path
  exact ⟨row.2.2.2.2.2.1 position root slot different index node present path,
    row.2.2.2.2.2.2 position root slot different index node present path⟩

end DuplicatePrefix.S05CompletedAncestryRangeRead

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CompletedAncestryRangeRead." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved ranged Read dependency {dependency}"
