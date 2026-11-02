import duplicate_prefix.S05CompletedAncestryNormal
import duplicate_prefix.S05CompletedAncestryWriteRoots
import duplicate_prefix.GeneralBorrowNormalOtherRootFrame
import duplicate_prefix.GeneralBorrowCompatibleLocationSifaConsistency
import duplicate_prefix.GeneralBorrowCompatibleNormalPossible

/-! One complete production concrete-source Write at a byte row. Initial
completed-source scalar tables derive normal and all other-root callbacks;
no operation outcome, legacy Row, chosen runtime mask or future rights are
caller premises. Completion is an explicit sufficient model, not an adopted
ordinary-input interpretation. -/
namespace DuplicatePrefix.S05CompletedAncestryConcreteWrite
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality GeneralBorrowProjection
open DuplicatePrefix.BorrowRangeAccess
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem access (tree : BorrowTree) (completion : Completion) (initial : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePath : Path tree selected source)
    (normalLocal : ∀ index node, tree.nodes.get index = some node → Path tree selected index →
      Below completion index source → LocalWrite
        ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))
    (normalForeign : ∀ index node, tree.nodes.get index = some node → Path tree selected index →
      ¬Below completion index source → ForeignWrite
        ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))
    (localRights : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
      ∀ index node, tree.nodes.get index = some node → Path tree root index → Below completion index source →
        LocalWrite ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))
    (foreignRights : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
      ∀ index node, tree.nodes.get index = some node → Path tree root index → ¬Below completion index source →
        ForeignWrite ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))
    (coherent : LocationCoherent tree initial protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree initial (some source) .Write protections mode range
    source_access_status result = none ∧
      LocationCoherent tree (source_access_location result) protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
      (∀ index node, tree.nodes.get index = some node → Path tree selected index →
        (source_access_location result).perms.get index =
          (tree.performNormalAccessAt initial source .Write protections mode).location.perms.get index) := by
  have fits : tree.nodes.data.size ≤ 4294967296 := by
    have size : tree.nodes.data.size = tree.nodes.size := rfl
    rw [size];omega
  obtain ⟨normal⟩ := S05CompletedAncestryNormal.normal tree completion initial protections complete formed depth fits
    selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath normalLocal normalForeign
  obtain ⟨sourceNode,sourcePresent⟩ := sourcePath.present
  obtain ⟨actual,found,parentless⟩ := complete.2.2.2.1 selectedPosition selected selectedSlot
  have same : actual = selectedNode := Option.some.inj (found.symm.trans selectedPresent)
  subst actual
  have rootPath := S05CompletedAncestryNormal.root_path tree initial protections formed selected source selectedNode
    selectedPresent parentless sourcePath
  have normalDone := DuplicatePrefixNormalKind.access tree initial protections source .Write mode
    (DuplicatePrefixNormalKind.of_normal tree initial protections source normal .Write) formed sourceNode sourcePresent coherent
  obtain ⟨forest⟩ := formed.forest initial protections
  have owned : GeneralBorrowCompatibleScopedNormal.Owned (source_normal_projection tree initial protections)
      source.toNat .Write normal.component := by
    intro index inside valid
    have size : (source_normal_projection tree initial protections).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
    exact normal.permissions .Write index inside (by rw [←size];exact valid)
  have afterProfile := (GeneralBorrowCompatibleLocationSifaConsistency.normal tree initial protections source .Write mode
    fits depth formed.children sourceNode sourcePresent forest normal.component owned profile).2.2
  have afterPossible := GeneralBorrowCompatibleNormalPossible.normal tree initial protections source .Write mode fits forest
    (GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree initial protections source sourceNode sourcePresent).1 normal possible
  have frame : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
      ∀ index node, tree.nodes.get index = some node → Path tree root index →
        (tree.performNormalAccessAt initial source .Write protections mode).location.perms.get index = initial.perms.get index := by
    intro position root slot different index node present path
    have data := Array.getElem?_eq_some_iff.mp slot
    have member : root ∈ tree.roots.toList := by
      rw [←data.2];exact Array.mem_toList_iff.mpr (Array.getElem_mem data.1)
    exact (GeneralBorrowNormalOtherRootFrame.access tree initial protections formed source selected root sourceNode sourcePresent
      normal rootPath member (Ne.symm different) .Write coherent mode).2.2.2 index node present path
  have final := S05CompletedAncestryWriteRoots.roots tree completion initial protections complete formed depth order
    selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath localRights foreignRights short
    (if mode == .SkipChildrenOfAccessed then source_min_exposed tree source else none) mode range
    (tree.performNormalAccessAt initial source .Write protections mode).location normalDone.2.2 afterProfile afterPossible frame
  have path : ((source_normal_projection tree initial protections).topology.ancestorPath source.toNat).getLast! = selected.toNat := by
    rw [List.getLast!_eq_getLast?_getD,rootPath];rfl
  have rootEq : (tree.performNormalAccessAt initial source .Write protections mode).access.root = selected.toNat :=
    (GeneralBorrowStorage.events_root _ _ .Write (source_normal_projection tree initial protections)).trans path
  dsimp only
  simp_tree_helpers
  simp only [normalDone.1,normalDone.2.1,rootEq,GeneralBorrowProjection.index_self,Option.bind_some,selectedPresent,Option.map_some]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  exact final

end DuplicatePrefix.S05CompletedAncestryConcreteWrite

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CompletedAncestryConcreteWrite." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved concrete Write dependency {dependency}"
