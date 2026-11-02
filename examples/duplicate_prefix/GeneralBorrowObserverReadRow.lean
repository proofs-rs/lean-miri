import duplicate_prefix.GeneralBorrowReadRowAccess
import duplicate_prefix.GeneralBorrowObserverReadTwoParents
namespace DuplicatePrefix.GeneralBorrowObserverReadRow
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection DuplicatePrefix.BorrowRangeAccess
open DuplicatePrefixResidualSupportAuthorization
open GeneralBorrowReadRowNormal (ReadRow)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
private theorem run (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (order : position = 0 → GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (read : Authorization tree location protections root position maximum .Read support)
    (write : Authorization tree location protections root position maximum .Write support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt location root maximum .Read protections (position != 0)
    result.status = .Completed ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = location.perms.get query) ∧
    Authorization tree result.location protections root position maximum .Read support ∧
    Authorization tree result.location protections root position maximum .Write support ∧
    (∀ query, ¬support query → result.location.perms.get query = location.perms.get query) := by
  by_cases primary : position = 0
  · subst position
    obtain ⟨done,_,_,_,cache,outside,sifa,gp,vacant,readAfter,writeAfter⟩ :=
      GeneralBorrowSnapshotOrderedPrimaryReadBothAuthorization.access tree location protections formed root maximum
        (order rfl) support read write coherent short profile possible
    exact ⟨done,cache,sifa,gp,vacant,readAfter,writeAfter,outside⟩
  · obtain ⟨depth⟩ := formed.depth
    obtain ⟨forest⟩ := formed.forest location protections
    obtain ⟨done,_,_,_,cache,outside,sifa,gp,vacant,readAfter,writeAfter⟩ :=
      GeneralBorrowSnapshotVirtualReadBothAuthorization.access_both tree location protections root position maximum
        support primary read write depth forest coherent short profile possible
    have virtual : (position != 0) = true := by simp [primary]
    simp only [virtual]
    exact ⟨done,cache,sifa,gp,vacant,readAfter,writeAfter,outside⟩


/-- Actual other-physical-root Read preserves an independent mutable observer
under arbitrary virtual protections. The root's finite raw callbacks derive
completion and outside-component framing. -/
theorem callback (tree : BorrowTree) (location : LocationTree) (actual virtual : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor observer selected : UniIndex) (anchorNode observerNode : TreeNode)
    (present : tree.nodeAt anchor = some anchorNode) (observerPresent : tree.nodeAt observer = some observerNode)
    (maximum : Option BorTag)
    (row : ReadRow tree location actual (some anchor) (some selected) maximum)
    (observerBoth : DuplicatePrefixBorrowAuthorization.Normal tree location virtual observer)
    (observerPath : ((source_normal_projection tree location virtual).topology.ancestorPath observer.toNat).getLast? = some selected.toNat)
    (distinct : tree.roots.toList.Nodup) (position : Nat) (valid : position < tree.roots.size)
    (different : selected ≠ tree.roots[position])
    (order : position = 0 → GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location actual)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location actual)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt location tree.roots[position] maximum .Read actual (position != 0)
    result.status = .Completed ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location actual ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location actual ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    Nonempty (ReadRow tree result.location actual (some anchor) (some selected) maximum) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree result.location virtual observer) := by
  obtain ⟨support,read,write⟩ := row.callbacks position valid (by simpa using different)
  obtain ⟨_,_,_,_,_,_,_,outside⟩ := run tree location actual formed tree.roots[position] position maximum
    support order read write coherent profile possible short
  have member : tree.roots[position] ∈ tree.roots.toList := Array.mem_toList_iff.mpr (Array.getElem_mem valid)
  obtain ⟨observerAfter,_⟩ := GeneralBorrowNormalOtherCallbackFrame.transport tree location _ virtual formed
    observer selected tree.roots[position] observerNode observerPresent observerBoth observerPath member different
    support read.present read.covers outside
  obtain ⟨done,cache,sifa,gp,rowAfter⟩ := GeneralBorrowReadRowAccess.callback tree location actual formed
    anchor selected anchorNode present maximum row distinct position valid different order coherent profile possible short
  exact ⟨done,cache,sifa,gp,rowAfter,⟨observerAfter⟩⟩

/-- The virtual table used while the len helper and its shared temporary are
live. This is ordinary endCall data, not an executed release assumption. -/
def virtual (global : GlobalState) (allocation : AllocId) (childTag temporaryTag : BorTag) : ProtectedTags :=
  ((global.endCall (({} : FrameState).addProtector allocation childTag)).endCall
    (({} : FrameState).addProtector allocation temporaryTag)).protectedTags

/-- Actual complete Read row, including all other-root callbacks, carries the independent two-level mutable observer. -/
theorem access_two_parents (tree : BorrowTree) (location : LocationTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (anchor selected : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (allocation : AllocId) (temporary observer : UniIndex) (temporaryNode observerNode : TreeNode)
    (childEdge : anchorNode.parent = some temporary)
    (temporaryPresent : tree.nodeAt temporary = some temporaryNode) (temporaryEdge : temporaryNode.parent = some observer)
    (observerPresent : tree.nodeAt observer = some observerNode)
    (childHidden : anchorNode.isExposed = false) (temporaryHidden : temporaryNode.isExposed = false)
    (observerBoth : DuplicatePrefixBorrowAuthorization.Normal tree location
      (virtual global allocation anchorNode.tag temporaryNode.tag) observer)
    (observerPath : ((source_normal_projection tree location (virtual global allocation anchorNode.tag temporaryNode.tag)).topology.ancestorPath observer.toNat).getLast? = some selected.toNat)
    (maximum : Option BorTag)
    (row : ReadRow tree location global.protectedTags (some anchor) (some selected) maximum)
    (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] →
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location global.protectedTags)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree location (some anchor) .Read global.protectedTags mode range
    source_access_status result = none ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree (source_access_location result) global.protectedTags ∧
    GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) global.protectedTags ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
    Nonempty (ReadRow tree (source_access_location result) global.protectedTags (some anchor) (some selected) maximum) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree (source_access_location result)
      (virtual global allocation anchorNode.tag temporaryNode.tag) observer) := by
  obtain ⟨done,outcome,cache,sifa,gp,afterRow⟩ := GeneralBorrowReadRowNormal.access tree location global.protectedTags runtime.formed.toGraphState anchor selected anchorNode present maximum row coherent profile possible short mode
  obtain ⟨sourceNormal⟩ := row.normal anchor rfl
  obtain ⟨_,_,observerAfter,sameComponent⟩ := GeneralBorrowObserverReadTwoParents.access tree location global runtime
    allocation anchor temporary observer anchorNode temporaryNode present childEdge temporaryPresent temporaryEdge
    childHidden temporaryHidden sourceNormal observerBoth mode
  have path : ((source_normal_projection tree location global.protectedTags).topology.ancestorPath anchor.toNat).getLast! = selected.toNat := by
    rw [List.getLast!_eq_getLast?_getD, row.rootPath anchor rfl]
    rfl
  have rootEq : (tree.performNormalAccessAt location anchor .Read global.protectedTags mode).access.root = selected.toNat :=
    (GeneralBorrowStorage.events_root _ _ .Read (source_normal_projection tree location global.protectedTags)).trans path
  obtain ⟨selectedNode,selectedPresent⟩ := row.rootPresent selected rfl
  have selectedLookup : tree.nodes.get selected = some selectedNode := selectedPresent
  have cutoff : maximum = some selectedNode.tag := by simpa [selectedPresent] using row.cutoff
  let property := fun current =>
    GeneralBorrowExposureCardinality.LocationCoherent tree current global.protectedTags ∧
    GeneralBorrowLocationSifaConsistency.Profile tree current global.protectedTags ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree current ∧
    Nonempty (ReadRow tree current global.protectedTags (some anchor) (some selected) maximum) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree current (virtual global allocation anchorNode.tag temporaryNode.tag) observer)
  have steps : ∀ position (valid : position < tree.roots.size), selected ≠ tree.roots[position] →
      ∀ current, property current →
      let result := tree.performWildcardAccessAt current tree.roots[position] maximum .Read global.protectedTags (position != 0)
      result.status = .Completed ∧ property result.location := by
    intro position valid different current good
    obtain ⟨cache,sifa,gp,⟨currentRow⟩,⟨currentObserver⟩⟩ := good
    apply callback tree current global.protectedTags (virtual global allocation anchorNode.tag temporaryNode.tag)
      runtime.formed.toGraphState anchor observer selected anchorNode observerNode present observerPresent maximum currentRow
      currentObserver observerPath distinct position valid different _ cache sifa gp short
    intro primary
    subst position
    exact order valid different
  have final := GeneralBorrowConcreteRootInvariant.roots tree global.protectedTags selected maximum
    (if mode == .SkipChildrenOfAccessed then source_min_exposed tree anchor else none) .Read mode range property steps
    ((tree.performNormalAccessAt location anchor .Read global.protectedTags mode).location,none,false)
    ⟨rfl,cache,sifa,gp,afterRow,⟨observerAfter⟩⟩
  dsimp only
  simp_tree_helpers
  simp only [done,outcome,rootEq,GeneralBorrowProjection.index_self,Option.bind_some,selectedLookup,Option.map_some]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  dsimp only [property] at final
  rw [cutoff] at final ⊢
  let after : Id GeneralBorrowConcreteRowAccess.State := forIn (List.range' 0 tree.roots.size)
    ((tree.performNormalAccessAt location anchor .Read global.protectedTags mode).location,none,false)
    (GeneralBorrowConcreteRowAccess.scan tree selected (some selectedNode.tag)
      (if mode == .SkipChildrenOfAccessed then source_min_exposed tree anchor else none) .Read global.protectedTags mode range)
  change after.2.1 = none ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree after.1 global.protectedTags ∧
    GeneralBorrowLocationSifaConsistency.Profile tree after.1 global.protectedTags ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree after.1 ∧
    Nonempty (ReadRow tree after.1 global.protectedTags (some anchor) (some selected) (some selectedNode.tag)) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree after.1 (virtual global allocation anchorNode.tag temporaryNode.tag) observer)
  exact final
end DuplicatePrefix.GeneralBorrowObserverReadRow
