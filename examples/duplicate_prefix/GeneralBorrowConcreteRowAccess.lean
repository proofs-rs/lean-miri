import duplicate_prefix.GeneralBorrowConcreteRowNormalAccess
import duplicate_prefix.GeneralBorrowConcreteRowPrimaryReadAccess
import duplicate_prefix.GeneralBorrowConcreteRowPrimaryWriteAccess
import duplicate_prefix.GeneralBorrowConcreteRowVirtualAccess
import duplicate_prefix.GeneralBorrowLoop
namespace DuplicatePrefix.GeneralBorrowConcreteRowAccess
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
abbrev State := LocationTree × Option BorrowTree.BorrowTreeAccessStatus × Bool

def scan (tree : BorrowTree) (selected : UniIndex) (maximum minimum : Option BorTag) (kind : AccessKind)
    (protections : ProtectedTags) (mode : ChildrenVisitMode) (range : ByteRange)
    (position : Nat) (state : State) : Id (ForInStep State) := Id.run do
  let (location,status,stop) := state
  if status.isNone && !stop then
    match tree.roots[position]? with
    | none => return .yield state
    | some root =>
      let rootTag := (tree.nodes.get root).map TreeNode.tag
      let past := match rootTag, minimum with
        | some tag, some minimum => tag.value > minimum.value
        | _, _ => false
      if mode == .SkipChildrenOfAccessed && past then
        return .yield (location,status,true)
      else if some selected != some root then
        let wildcard := tree.performWildcardAccessAt location root maximum kind protections (position != 0)
        if wildcard.status != .Completed then
          return .yield (wildcard.location,some (.WildcardFailure range wildcard.status),stop)
        else
          return .yield (wildcard.location,status,stop)
  return .yield state

abbrev Good (tree : BorrowTree) (protections : ProtectedTags) (anchor selected : UniIndex)
    (maximum : Option BorTag) (state : State) : Prop :=
  state.2.1 = none ∧
  GeneralBorrowExposureCardinality.LocationCoherent tree state.1 protections ∧
  GeneralBorrowLocationSifaConsistency.Profile tree state.1 protections ∧
  GeneralBorrowSnapshotReadRuntime.GlobalPossible tree state.1 ∧
  Nonempty (DuplicatePrefixBorrowAuthorization.Row tree state.1 protections (some anchor) (some selected) maximum)

theorem roots (tree : BorrowTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (maximum minimum : Option BorTag) (kind : AccessKind) (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] →
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) (range : ByteRange)
    (initial : State) (good : Good tree protections anchor selected maximum initial) :
    Good tree protections anchor selected maximum
      (forIn (List.range' 0 tree.roots.size) initial (scan tree selected maximum minimum kind protections mode range) : Id State) := by
  apply GeneralBorrowLoop.list_invariant _ _ _ _ initial good
  intro position member state good
  rcases state with ⟨location,status,stop⟩
  rcases good with ⟨statusEq,coherent,profile,possible,⟨row⟩⟩
  dsimp only at statusEq
  subst status
  have valid : position < tree.roots.size := by
    have bounded := List.mem_range'_1.mp member
    simpa using bounded.2
  have lookup := Array.getElem?_eq_getElem valid
  by_cases stopped : stop = true
  · subst stop
    simpa [scan,Good] using (show Good tree protections anchor selected maximum (location,none,true) from ⟨rfl,coherent,profile,possible,⟨row⟩⟩)
  have stopFalse : stop = false := by cases stop <;> simp_all
  subst stop
  by_cases early : (mode == .SkipChildrenOfAccessed &&
      (match (tree.nodes.get tree.roots[position]).map TreeNode.tag, minimum with
      | some tag, some minimum => tag.value > minimum.value | _, _ => false)) = true
  · simpa [scan,lookup,early,Good] using (show Good tree protections anchor selected maximum (location,none,true) from ⟨rfl,coherent,profile,possible,⟨row⟩⟩)
  by_cases same : selected = tree.roots[position]
  · simpa [scan,lookup,early,same,Good] using (show Good tree protections anchor selected maximum (location,none,false) from ⟨rfl,coherent,profile,possible,⟨row⟩⟩)
  have callback : let result := tree.performWildcardAccessAt location tree.roots[position] maximum kind protections (position != 0)
      result.status = .Completed ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Row tree result.location protections (some anchor) (some selected) maximum) := by
    by_cases primary : position = 0
    · subst position
      cases kind with
      | Read =>
        obtain ⟨a,b,c,d,_,e⟩ := GeneralBorrowConcreteRowPrimaryReadAccess.access tree location protections formed anchor selected anchorNode present maximum row distinct valid same (order valid same) coherent profile possible short
        exact ⟨a,b,c,d,e⟩
      | Write =>
        obtain ⟨a,b,c,d,_,e⟩ := GeneralBorrowConcreteRowPrimaryWriteAccess.access tree location protections formed anchor selected anchorNode present maximum row distinct valid same (order valid same) coherent profile possible short
        exact ⟨a,b,c,d,e⟩
    · obtain ⟨a,b,c,d,_,e⟩ := GeneralBorrowConcreteRowVirtualAccess.access tree location protections formed anchor selected anchorNode present maximum row distinct position valid primary same kind coherent profile possible short
      have virtual : (position != 0) = true := by simp [primary]
      simp only [virtual]
      exact ⟨a,b,c,d,e⟩
  simpa [scan,lookup,early,same,callback.1,Good] using
    (show Good tree protections anchor selected maximum ((tree.performWildcardAccessAt location tree.roots[position] maximum kind protections (position != 0)).location,none,false) from ⟨rfl,callback.2⟩)

/-- Literal concrete-source Read or Write, including either visit mode and arbitrary
min-exposed early stopping. ParentTagOrder is an explicit coverage obligation. -/
theorem access_when_primary (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (maximum : Option BorTag) (kind : AccessKind)
    (row : DuplicatePrefixBorrowAuthorization.Row tree location protections (some anchor) (some selected) maximum)
    (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] →
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree location (some anchor) kind protections mode range
    source_access_status result = none ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree (source_access_location result) protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Row tree (source_access_location result) protections (some anchor) (some selected) maximum) := by
  obtain ⟨done,outcome,cache,sifa,gp,afterRow⟩ := GeneralBorrowConcreteRowNormalAccess.access tree location protections formed anchor selected anchorNode present maximum row kind mode coherent profile possible short
  have path : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast! = selected.toNat := by
    rw [List.getLast!_eq_getLast?_getD, row.rootPath anchor rfl]
    rfl
  have rootEq : (tree.performNormalAccessAt location anchor kind protections mode).access.root = selected.toNat :=
    (GeneralBorrowStorage.events_root _ _ kind (source_normal_projection tree location protections)).trans path
  obtain ⟨selectedNode,selectedPresent⟩ := row.rootPresent selected rfl
  have selectedLookup : tree.nodes.get selected = some selectedNode := selectedPresent
  have cutoff : maximum = some selectedNode.tag := by simpa [selectedPresent] using row.cutoff
  have final := roots tree protections formed anchor selected anchorNode present maximum
    (if mode == .SkipChildrenOfAccessed then source_min_exposed tree anchor else none) kind
    distinct order short mode range ((tree.performNormalAccessAt location anchor kind protections mode).location,none,false)
    ⟨rfl,cache,sifa,gp,afterRow⟩
  dsimp only
  simp_tree_helpers
  simp only [done,outcome,rootEq,GeneralBorrowProjection.index_self,Option.bind_some,selectedLookup,Option.map_some]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  rw [cutoff] at final ⊢
  change Good tree protections anchor selected (some selectedNode.tag)
    (forIn (List.range' 0 tree.roots.size)
      ((tree.performNormalAccessAt location anchor kind protections mode).location,none,false)
      (scan tree selected (some selectedNode.tag)
        (if mode == .SkipChildrenOfAccessed then source_min_exposed tree anchor else none) kind protections mode range) : Id State)
  exact final
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (maximum : Option BorTag) (kind : AccessKind)
    (row : DuplicatePrefixBorrowAuthorization.Row tree location protections (some anchor) (some selected) maximum)
    (distinct : tree.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree location (some anchor) kind protections mode range
    source_access_status result = none ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree (source_access_location result) protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Row tree (source_access_location result) protections (some anchor) (some selected) maximum) := by
  exact access_when_primary tree location protections formed anchor selected anchorNode present maximum kind row distinct
    (fun _ _ => order) coherent profile possible short mode range
end DuplicatePrefix.GeneralBorrowConcreteRowAccess
