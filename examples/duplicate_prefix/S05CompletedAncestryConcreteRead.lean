import duplicate_prefix.S05CompletedAncestryReadRoots
import duplicate_prefix.GeneralBorrowPhysicalNormalCapability
import duplicate_prefix.S05CompletedAncestryNormal
import duplicate_prefix.GeneralBorrowNormalOtherRootFrame
import duplicate_prefix.GeneralBorrowReadCapabilityNormal

/-! A complete production concrete-source Read. The actual reader requires
only its initial Read scalar table; a separate completed-ancestry authority
anchor governs other roots. No legacy Row, operation outcome or future rights
are caller premises. The completion remains an unadopted sufficient model. -/
namespace DuplicatePrefix.S05CompletedAncestryConcreteRead
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
    (reader : UniIndex) (readerPath : Path tree selected reader)
    (normalRights : ∀ index node, tree.nodes.get index = some node → Path tree selected index →
      DuplicatePrefixScalarAuthorization.Compatible
        ((initial.perms.get index).getD node.defaultLocationState) .Read
        (GeneralBorrowAnchor.relation (source_normal_projection tree initial protections) reader.toNat index.toNat)
        (protections.contains node.tag))
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
    let result := source_tree_access_at tree initial (some reader) .Read protections mode range
    source_access_status result = none ∧
      LocationCoherent tree (source_access_location result) protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
      (∀ index node, tree.nodes.get index = some node → Path tree selected index →
        (source_access_location result).perms.get index =
          (tree.performNormalAccessAt initial reader .Read protections mode).location.perms.get index) ∧
      (∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
        ∀ index node, tree.nodes.get index = some node → Path tree root index → Below completion index source →
          LocalWrite (((source_access_location result).perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) ∧
      (∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
        ∀ index node, tree.nodes.get index = some node → Path tree root index → ¬Below completion index source →
          ForeignWrite (((source_access_location result).perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) := by
  have fits : tree.nodes.data.size ≤ 4294967296 := by
    have size : tree.nodes.data.size = tree.nodes.size := rfl
    rw [size];omega
  obtain ⟨actual,found,parentless⟩ := complete.2.2.2.1 selectedPosition selected selectedSlot
  have same : actual = selectedNode := Option.some.inj (found.symm.trans selectedPresent)
  subst actual
  obtain ⟨normal⟩ := GeneralBorrowPhysicalNormalCapability.of_physical_component tree initial protections
    formed fits selected reader selectedNode selectedPresent parentless readerPath .Read normalRights
  obtain ⟨readerNode,readerPresent⟩ := readerPath.present
  have rootPath := S05CompletedAncestryNormal.root_path tree initial protections formed selected reader selectedNode
    selectedPresent parentless readerPath
  have normalDone := GeneralBorrowReadCapabilityNormal.access tree initial protections formed reader readerNode
    readerPresent normal coherent profile possible short mode
  have frame : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
      ∀ index node, tree.nodes.get index = some node → Path tree root index →
        (tree.performNormalAccessAt initial reader .Read protections mode).location.perms.get index = initial.perms.get index := by
    intro position root slot different index node present path
    have data := Array.getElem?_eq_some_iff.mp slot
    have member : root ∈ tree.roots.toList := by
      rw [←data.2];exact Array.mem_toList_iff.mpr (Array.getElem_mem data.1)
    exact (GeneralBorrowNormalOtherRootFrame.access_kind tree initial protections formed reader selected root readerNode
      readerPresent .Read normal rootPath member (Ne.symm different) coherent mode).2.2.2 index node present path
  have final := S05CompletedAncestryReadRoots.roots tree completion
    (tree.performNormalAccessAt initial reader .Read protections mode).location protections complete formed depth order
    selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath short
    (if mode == .SkipChildrenOfAccessed then source_min_exposed tree reader else none) mode range
    normalDone.2.2.1 normalDone.2.2.2.1 normalDone.2.2.2.2.1
    (fun position root slot different index node present path below => by
      rw [frame position root slot different index node present path]
      exact localRights position root slot different index node present path below)
    (fun position root slot different index node present path below => by
      rw [frame position root slot different index node present path]
      exact foreignRights position root slot different index node present path below)
  have path : ((source_normal_projection tree initial protections).topology.ancestorPath reader.toNat).getLast! = selected.toNat := by
    rw [List.getLast!_eq_getLast?_getD,rootPath];rfl
  have rootEq : (tree.performNormalAccessAt initial reader .Read protections mode).access.root = selected.toNat :=
    (GeneralBorrowStorage.events_root _ _ .Read (source_normal_projection tree initial protections)).trans path
  dsimp only
  simp_tree_helpers
  simp only [normalDone.1,normalDone.2.1,rootEq,GeneralBorrowProjection.index_self,Option.bind_some,selectedPresent,Option.map_some]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  exact ⟨final.1,final.2.1,final.2.2.1,final.2.2.2.1,final.2.2.2.2.2,final.2.2.2.2.1.1,final.2.2.2.2.1.2⟩

end DuplicatePrefix.S05CompletedAncestryConcreteRead
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CompletedAncestryConcreteRead." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved concrete Read dependency {dependency}"
