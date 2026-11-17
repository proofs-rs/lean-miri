import duplicate_prefix.GeneralBorrowConcreteRootInvariant
import duplicate_prefix.GeneralBorrowReadRowNormal
namespace DuplicatePrefix.GeneralBorrowReadRowAccess
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection DuplicatePrefix.BorrowRangeAccess
open DuplicatePrefixResidualSupportAuthorization
open GeneralBorrowReadRowNormal (ReadRow)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

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

/-- Every actual other-root Read retains the selected Read-only normal
capability and both residual candidates. All callback results are derived. -/
theorem callback (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (maximum : Option BorTag)
    (row : ReadRow tree location protections (some anchor) (some selected) maximum)
    (distinct : tree.roots.toList.Nodup) (position : Nat) (valid : position < tree.roots.size)
    (different : selected ≠ tree.roots[position])
    (order : position = 0 → GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt location tree.roots[position] maximum .Read protections (position != 0)
    result.status = .Completed ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    Nonempty (ReadRow tree result.location protections (some anchor) (some selected) maximum) := by
  have selectedDifferent : some selected ≠ some tree.roots[position] := by simpa using different
  obtain ⟨support,read,write⟩ := row.callbacks position valid selectedDifferent
  obtain ⟨done,cache,sifa,gp,vacant,readAfter,writeAfter,outside⟩ := run tree location protections formed
    tree.roots[position] position maximum support order read write coherent profile possible short
  have member : tree.roots[position] ∈ tree.roots.toList := Array.mem_toList_iff.mpr (Array.getElem_mem valid)
  obtain ⟨normal⟩ := row.normal anchor rfl
  have path : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? = some selected.toNat := by
    simpa using row.rootPath anchor rfl
  obtain ⟨normalAfter,_⟩ := GeneralBorrowReadCapabilityFrames.after_callback tree location _ protections formed
    anchor selected tree.roots[position] anchorNode present normal path member different support read.present read.covers outside
  refine ⟨done,cache,sifa,gp,⟨{
    wildcard := row.wildcard,rootPath := row.rootPath,rootPresent := row.rootPresent,
    cutoff := row.cutoff,normal := ?_,callbacks := ?_}⟩⟩
  · intro source equal
    have equal : source = anchor := Option.some.inj equal.symm
    subst source
    exact ⟨normalAfter⟩
  · intro other otherValid selectedOther
    by_cases same : other = position
    · subst other
      exact ⟨support,readAfter,writeAfter⟩
    · obtain ⟨otherSupport,otherRead,otherWrite⟩ := row.callbacks other otherValid selectedOther
      have otherMember : tree.roots[other] ∈ tree.roots.toList := Array.mem_toList_iff.mpr (Array.getElem_mem otherValid)
      have rootsDifferent : tree.roots[position] ≠ tree.roots[other] := by
        intro equal
        have positions : position = other := by
          apply distinct.getElem_inj.mp
          change tree.roots[position] = tree.roots[other]
          exact equal
        exact same positions.symm
      have transport (kind : AccessKind)
          (authorization : Authorization tree location protections tree.roots[other] other maximum kind otherSupport) :=
        GeneralBorrowRootLocalAuthorization.authorization_other tree location _ protections formed tree.roots[position]
          tree.roots[other] member otherMember rootsDifferent support otherSupport read.covers other maximum kind authorization outside
      exact ⟨otherSupport,transport .Read otherRead,transport .Write otherWrite⟩

theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (maximum : Option BorTag)
    (row : ReadRow tree location protections (some anchor) (some selected) maximum)
    (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] →
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree location (some anchor) .Read protections mode range
    source_access_status result = none ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree (source_access_location result) protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
    Nonempty (ReadRow tree (source_access_location result) protections (some anchor) (some selected) maximum) := by
  obtain ⟨done,outcome,cache,sifa,gp,afterRow⟩ := GeneralBorrowReadRowNormal.access tree location protections formed anchor selected anchorNode present maximum row coherent profile possible short mode
  have path : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast! = selected.toNat := by
    rw [List.getLast!_eq_getLast?_getD, row.rootPath anchor rfl]
    rfl
  have rootEq : (tree.performNormalAccessAt location anchor .Read protections mode).access.root = selected.toNat :=
    (GeneralBorrowStorage.events_root _ _ .Read (source_normal_projection tree location protections)).trans path
  obtain ⟨selectedNode,selectedPresent⟩ := row.rootPresent selected rfl
  have selectedLookup : tree.nodes.get selected = some selectedNode := selectedPresent
  have cutoff : maximum = some selectedNode.tag := by simpa [selectedPresent] using row.cutoff
  let property := fun current =>
    GeneralBorrowExposureCardinality.LocationCoherent tree current protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree current protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree current ∧
    Nonempty (ReadRow tree current protections (some anchor) (some selected) maximum)
  have steps : ∀ position (valid : position < tree.roots.size), selected ≠ tree.roots[position] →
      ∀ current, property current →
      let result := tree.performWildcardAccessAt current tree.roots[position] maximum .Read protections (position != 0)
      result.status = .Completed ∧ property result.location := by
    intro position valid different current good
    obtain ⟨cache,sifa,gp,⟨currentRow⟩⟩ := good
    apply callback tree current protections formed anchor selected anchorNode present maximum currentRow distinct position valid different _ cache sifa gp short
    intro primary
    subst position
    exact order valid different
  have final := GeneralBorrowConcreteRootInvariant.roots tree protections selected maximum
    (if mode == .SkipChildrenOfAccessed then source_min_exposed tree anchor else none) .Read mode range property steps
    ((tree.performNormalAccessAt location anchor .Read protections mode).location,none,false)
    ⟨rfl,cache,sifa,gp,afterRow⟩
  dsimp only
  simp_tree_helpers
  simp only [done,outcome,rootEq,GeneralBorrowProjection.index_self,Option.bind_some,selectedLookup,Option.map_some]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  dsimp only [property] at final
  rw [cutoff] at final ⊢
  let after : Id GeneralBorrowConcreteRowAccess.State := forIn (List.range' 0 tree.roots.size)
    ((tree.performNormalAccessAt location anchor .Read protections mode).location,none,false)
    (GeneralBorrowConcreteRowAccess.scan tree selected (some selectedNode.tag)
      (if mode == .SkipChildrenOfAccessed then source_min_exposed tree anchor else none) .Read protections mode range)
  change after.2.1 = none ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree after.1 protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree after.1 protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree after.1 ∧
    Nonempty (ReadRow tree after.1 protections (some anchor) (some selected) (some selectedNode.tag))
  exact final
end DuplicatePrefix.GeneralBorrowReadRowAccess
