import duplicate_prefix.GeneralBorrowConcreteRangeEntry
import duplicate_prefix.S05CompletedAncestryConcreteRead
import duplicate_prefix.GeneralBorrowNormalComponentNormalization

/-! Actual ranged concrete Read with a Read-only physical reader and separate
other-root mutable-ancestry authority. Saved initial segment data supplies the
input; the actual visitor preserves the other-root scalar tables. -/
namespace DuplicatePrefix.S05CompletedAncestryReadCapability
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality GeneralBorrowProjection
open GeneralRangeMapOrigins GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

private theorem capability_selected (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree) (root reader : UniIndex)
    (readerPath : GeneralBorrowExposedNonleafPrimaryPath.Path tree root reader)
    (normal : DuplicatePrefixNormalKind.Capability tree location protections reader .Read) :
    ∀ index node, tree.nodes.get index = some node → GeneralBorrowExposedNonleafPrimaryPath.Path tree root index →
      DuplicatePrefixScalarAuthorization.Compatible (CandidateStableCallOwnership.RawState location index node) .Read
        (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) reader.toNat index.toNat)
        (protections.contains node.tag) := by
  obtain ⟨forest⟩ := formed.forest location protections
  have projected := GeneralBorrowPhysicalRootPath.projection_desc tree location protections root reader readerPath
  have rootInside := GeneralBorrowNormalComponentNormalization.contains_ancestor _ reader.toNat normal.component
    root.toNat reader.toNat projected normal.component.anchor
  intro index node present path
  have projected := GeneralBorrowPhysicalRootPath.projection_desc tree location protections root index path
  have supported := GeneralBorrowNormalComponentNormalization.contains_descendant _ forest reader.toNat normal.component
    root.toNat index.toNat projected rootInside
  obtain ⟨state,stored,compatible⟩ := normal.permissions index.toNat supported
    (GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node present)
  have actualState := projection_state tree location protections index.toNat index node (index_self index) rfl present
  have equal : state = CandidateStableCallOwnership.RawState location index node := Option.some.inj (stored.symm.trans actualState)
  subst state
  rw [GeneralBorrowNormalPermissionMetadata.held tree location protections index node present] at compatible
  exact compatible

theorem access (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
    (complete : Completes tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source reader : UniIndex) (selectedNode readerNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePath : Path tree selected source)
    (readerPresent : tree.nodes.get reader = some readerNode) (readerPath : Path tree selected reader)
    (offset len : Size) (lower upper : UInt64)
    (owned : OwnedOn (fun location => GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
      Nonempty (DuplicatePrefixNormalKind.Capability tree location protections reader .Read) ∧
      (∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
        ∀ index node, tree.nodes.get index = some node → Path tree root index →
          (Below completion index source → LocalWrite
            ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) ∧
          (¬Below completion index source → ForeignWrite
            ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))))
      lower upper tree.locations)
    (well : tree.locations.WellFormed)
    (runtime : Every (fun location => LocationCoherent tree location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : lower.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes + len.bytes).toNat ≤ upper.toNat)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) :
    GeneralBorrowConcreteRangeInvariant.Contract tree
      (fun location => GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
      Nonempty (DuplicatePrefixNormalKind.Capability tree location protections reader .Read) ∧
      (∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
        ∀ index node, tree.nodes.get index = some node → Path tree root index →
          (Below completion index source → LocalWrite
            ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) ∧
          (¬Below completion index source → ForeignWrite
            ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))))
      (fun location => LocationCoherent tree location protections ∧
        GeneralBorrowLocationSifaConsistency.Profile tree location protections ∧
        GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
      (fun before after => before = after ∨
        ∀ index node, tree.nodes.get index = some node → Path tree selected index →
          after.perms.get index =
            (tree.performNormalAccessAt before reader .Read protections mode).location.perms.get index)
      lower upper (tree.performBorrowAccessRange (.concrete readerNode.tag) offset len .Read protections mode) := by
  have mapped : tree.indexOfTag readerNode.tag = some reader :=
    (complete.2.2.2.2.1 reader readerNode readerPresent).1
  apply GeneralBorrowConcreteRangeEntry.access tree protections readerNode.tag reader mapped offset len .Read mode
    _ _ _ _ (fun _ initial => initial) (fun _ => Or.inl rfl) _
    lower upper owned well runtime bounds requestLower requestUpper
  intro location authority representation range
  obtain ⟨normal⟩ := authority.2.1
  have rights := capability_selected tree location protections formed selected reader readerPath normal
  have normalDone := GeneralBorrowReadCapabilityNormal.access tree location protections formed reader readerNode
    readerPresent normal representation.1 representation.2.1 representation.2.2 short mode
  have row := S05CompletedAncestryConcreteRead.access tree completion location protections complete formed depth order
    selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath reader readerPath rights
    (fun position root slot different index node present path below =>
      (authority.2.2 position root slot different index node present path).1 below)
    (fun position root slot different index node present path outside =>
      (authority.2.2 position root slot different index node present path).2 outside)
    representation.1 representation.2.1 authority.1 short mode range
  obtain ⟨afterNormal,componentEq⟩ := normalDone.2.2.2.2.2
  have afterRights := capability_selected tree _ protections formed selected reader readerPath afterNormal
  obtain ⟨actual,found,parentless⟩ := complete.2.2.2.1 selectedPosition selected selectedSlot
  have same : actual = selectedNode := Option.some.inj (found.symm.trans selectedPresent)
  subst actual
  have fits : tree.nodes.data.size ≤ 4294967296 := by change tree.nodes.size ≤ _;omega
  have cap := GeneralBorrowPhysicalNormalCapability.of_physical_component tree
    (source_access_location (source_tree_access_at tree location (some reader) .Read protections mode range))
    protections formed fits selected reader selectedNode selectedPresent parentless readerPath .Read (by
      intro index node present path
      have right := afterRights index node present path
      unfold CandidateStableCallOwnership.RawState at right
      rw [←row.2.2.2.2.1 index node present path] at right
      exact right)
  refine ⟨row.1,⟨row.2.2.2.1,cap,?_⟩,⟨row.2.1,row.2.2.1,row.2.2.2.1⟩,Or.inr row.2.2.2.2.1⟩
  intro position root slot different index node present path
  exact ⟨row.2.2.2.2.2.1 position root slot different index node present path,
    row.2.2.2.2.2.2 position root slot different index node present path⟩

end DuplicatePrefix.S05CompletedAncestryReadCapability

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CompletedAncestryReadCapability." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved ranged Read dependency {dependency}"
