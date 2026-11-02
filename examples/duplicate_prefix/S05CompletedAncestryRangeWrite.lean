import duplicate_prefix.GeneralBorrowConcreteRangeEntry
import duplicate_prefix.S05CompletedAncestryConcreteWrite

/-! Actual ranged concrete Write from initial scalar authority on intersecting
rows. Input authority is consumed on saved prepared segments, without a claim
that all Write authority survives. Ordinary-input coverage remains separate. -/
namespace DuplicatePrefix.S05CompletedAncestryRangeWrite
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality
open GeneralRangeMapOrigins GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

theorem access (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
    (complete : Completes tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode)
    (sourcePresent : tree.nodes.get source = some sourceNode) (sourcePath : Path tree selected source)
    (offset len : Size) (lower upper : UInt64)
    (owned : OwnedOn (fun location => GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
      ∀ index node, tree.nodes.get index = some node →
        (Below completion index source → LocalWrite
          ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) ∧
        (¬Below completion index source → ForeignWrite
          ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)))
      lower upper tree.locations)
    (well : tree.locations.WellFormed)
    (runtime : Every (fun location => LocationCoherent tree location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree location protections) tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : lower.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes + len.bytes).toNat ≤ upper.toNat)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) :
    GeneralBorrowConcreteRangeInvariant.Contract tree
      (GeneralBorrowSnapshotReadRuntime.GlobalPossible tree)
      (fun location => LocationCoherent tree location protections ∧
        GeneralBorrowLocationSifaConsistency.Profile tree location protections)
      (fun before after => before = after ∨
        ∀ index node, tree.nodes.get index = some node → Path tree selected index →
          after.perms.get index =
            (tree.performNormalAccessAt before source .Write protections mode).location.perms.get index)
      lower upper (tree.performBorrowAccessRange (.concrete sourceNode.tag) offset len .Write protections mode) := by
  have mapped : tree.indexOfTag sourceNode.tag = some source :=
    (complete.2.2.2.2.1 source sourceNode sourcePresent).1
  apply GeneralBorrowConcreteRangeEntry.access tree protections sourceNode.tag source mapped offset len .Write mode
    _ _ _ _ (fun _ initial => initial.1) (fun _ => Or.inl rfl) _ lower upper owned well runtime bounds requestLower requestUpper
  intro location authority representation range
  have row := S05CompletedAncestryConcreteWrite.access tree completion location protections complete formed depth order
    selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath
    (fun index node present _ below => (authority.2 index node present).1 below)
    (fun index node present _ outside => (authority.2 index node present).2 outside)
    (fun _ _ _ _ index node present _ below => (authority.2 index node present).1 below)
    (fun _ _ _ _ index node present _ outside => (authority.2 index node present).2 outside)
    representation.1 representation.2 authority.1 short mode range
  exact ⟨row.1,row.2.2.2.1,⟨row.2.1,row.2.2.1⟩,Or.inr row.2.2.2.2⟩

end DuplicatePrefix.S05CompletedAncestryRangeWrite

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CompletedAncestryRangeWrite." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved ranged Write dependency {dependency}"
