import duplicate_prefix.GeneralBorrowProtectedReadSingleRoot
import duplicate_prefix.GeneralBorrowRange
import duplicate_prefix.GeneralBorrowRangeCallbackOutput
import duplicate_prefix.GeneralBorrowConstructorPriorPermissionRange
namespace DuplicatePrefix.GeneralBorrowProtectedReadRange
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralRangeMapOrigins
open DuplicatePrefix.GeneralBorrowConstructorPriorPermission
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
def LocationCompatible (tree : BorrowTree) (protections : ProtectedTags) (anchor : UniIndex) (location : LocationTree) : Prop :=
  Nonempty (GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology) ∧
  anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size ∧
  ∀ index,index < (source_normal_projection tree location protections).topology.nodes.size → ∃ state,
    (source_normal_projection tree location protections).stateAt index = some state ∧
    GeneralBorrowProtectedReadCompatible.Compatible state
      (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat index)
      ((source_normal_projection tree location protections).protectedNodes.contains index)
theorem access (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (anchor root : UniIndex)
    (offset len : Size) (mode : ChildrenVisitMode)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (well : tree.locations.WellFormed)
    (all : Every (LocationCompatible tree protections anchor) tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat) :
    (tree.performNormalAccessRange tag offset len .Read protections mode).status = .Completed := by
  let prepared := tree.locations.iterMut offset len
  have preparedGood := GeneralRangeMapSafety.iter_mut (LocationCompatible tree protections anchor)
    tree.locations offset len well all bounds
  unfold BorrowTree.performNormalAccessRange BorrowTree.performBorrowAccessRange
  simp only [tagPresent,Option.isNone_some,Bool.false_eq_true,↓reduceIte]
  simp only [Id.run,bind,pure,preparedGood.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  let property := fun state : DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus =>
    state.2.2 = .Completed ∧ state.1.entries.size = prepared.state.entries.size
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
      property state → property (scan cursor state).value := by
    intro cursor member state good
    rcases state with ⟨current,visited,status⟩
    rcases good with ⟨statusEq,sizeEq⟩
    dsimp only at statusEq sizeEq
    subst status
    have cursorBound : cursor < prepared.positions.size := by
      have bounded := List.mem_range'_1.mp member
      simpa using bounded.2
    have segmentBound : cursor < prepared.segments.size := by
      rw [←preparedGood.lengths]
      exact cursorBound
    let position := prepared.positions[cursor]'cursorBound
    let segment := prepared.segments[cursor]'segmentBound
    obtain ⟨positionBound,selected⟩ := preparedGood.selected cursor cursorBound
    have ownedHere : LocationCompatible tree protections anchor segment.data := by
      rw [show segment = prepared.state.entries[position]'positionBound from selected]
      exact preparedGood.every position positionBound
    obtain ⟨⟨forest⟩,valid,compatible⟩ := ownedHere
    have accessGood := GeneralBorrowProtectedReadSingleRoot.access_at tree segment.data protections anchor root mode segment.range
      forest valid compatible depth children anchorNode anchorPresent roots covered
    let access := source_tree_access_at tree segment.data (some anchor) .Read protections mode segment.range
    let mutation := current.setAtPos position (source_access_location access)
    have currentBound : position < current.entries.size := by
      rw [sizeEq]
      exact positionBound
    have positionLookup : (tree.locations.iterMut offset len).positions[cursor]? = some position :=
      Array.getElem?_eq_getElem cursorBound
    have segmentLookup : (tree.locations.iterMut offset len).segments[cursor]? = some segment :=
      Array.getElem?_eq_getElem segmentBound
    have actual : scan cursor (current,visited,.Completed) =
        .yield (mutation.state,visited.push ⟨segment.range,source_access_normal access⟩,.Completed) := by
      simp only [scan,beq_self_eq_true,↓reduceIte,
        positionLookup,segmentLookup,
        setAtPos_success current position currentBound,accessGood]
      rfl
    rw [actual]
    refine ⟨rfl,?_⟩
    exact (setAtPos_length current position currentBound (source_access_location access)).trans sizeEq
  have initial : property (prepared.state,#[],.Completed) := ⟨rfl,rfl⟩
  exact (GeneralBorrowLoop.list_invariant _ scan property step _ initial).1

theorem geometry (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (anchor root : UniIndex)
    (offset len : Size) (mode : ChildrenVisitMode)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (well : tree.locations.WellFormed)
    (all : Every (LocationCompatible tree protections anchor) tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat) :
    let result := tree.performNormalAccessRange tag offset len .Read protections mode
    result.tree.locations.WellFormed ∧ result.tree.locations.size = tree.locations.size := by
  let prepared := tree.locations.iterMut offset len
  have preparedGood := GeneralRangeMapSafety.iter_mut (LocationCompatible tree protections anchor)
    tree.locations offset len well all bounds
  unfold BorrowTree.performNormalAccessRange BorrowTree.performBorrowAccessRange
  simp only [tagPresent,Option.isNone_some,Bool.false_eq_true,↓reduceIte]
  simp only [Id.run,bind,pure,preparedGood.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  let property := fun state : DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus =>
    state.2.2 = .Completed ∧ state.1.entries.size = prepared.state.entries.size ∧ state.1.WellFormed ∧ state.1.size = tree.locations.size
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
      property state → property (scan cursor state).value := by
    intro cursor member state good
    rcases state with ⟨current,visited,status⟩
    rcases good with ⟨statusEq,sizeEq,currentWell,currentSize⟩
    dsimp only at statusEq sizeEq
    subst status
    have cursorBound : cursor < prepared.positions.size := by
      have bounded := List.mem_range'_1.mp member
      simpa using bounded.2
    have segmentBound : cursor < prepared.segments.size := by
      rw [←preparedGood.lengths]
      exact cursorBound
    let position := prepared.positions[cursor]'cursorBound
    let segment := prepared.segments[cursor]'segmentBound
    obtain ⟨positionBound,selected⟩ := preparedGood.selected cursor cursorBound
    have ownedHere : LocationCompatible tree protections anchor segment.data := by
      rw [show segment = prepared.state.entries[position]'positionBound from selected]
      exact preparedGood.every position positionBound
    obtain ⟨⟨forest⟩,valid,compatible⟩ := ownedHere
    have accessGood := GeneralBorrowProtectedReadSingleRoot.access_at tree segment.data protections anchor root mode segment.range
      forest valid compatible depth children anchorNode anchorPresent roots covered
    let access := source_tree_access_at tree segment.data (some anchor) .Read protections mode segment.range
    let mutation := current.setAtPos position (source_access_location access)
    have currentBound : position < current.entries.size := by
      rw [sizeEq]
      exact positionBound
    have positionLookup : (tree.locations.iterMut offset len).positions[cursor]? = some position :=
      Array.getElem?_eq_getElem cursorBound
    have segmentLookup : (tree.locations.iterMut offset len).segments[cursor]? = some segment :=
      Array.getElem?_eq_getElem segmentBound
    have actual : scan cursor (current,visited,.Completed) =
        .yield (mutation.state,visited.push ⟨segment.range,source_access_normal access⟩,.Completed) := by
      simp only [scan,beq_self_eq_true,↓reduceIte,
        positionLookup,segmentLookup,
        setAtPos_success current position currentBound,accessGood]
      rfl
    rw [actual]
    refine ⟨rfl,(setAtPos_length current position currentBound (source_access_location access)).trans sizeEq,?_,?_⟩
    · change (current.setAtPos position (source_access_location access)).state.WellFormed
      rw [setAtPos_exact current position currentBound]
      exact replaced_wellFormed current position currentBound _ currentWell
    · change (current.setAtPos position (source_access_location access)).state.size = tree.locations.size
      rw [setAtPos_exact current position currentBound]
      exact (replaced_size current position currentBound _).trans currentSize
  have initial : property (prepared.state,#[],.Completed) := ⟨rfl,rfl,preparedGood.wellFormed,by exact congrArg Size.ofBytes preparedGood.capacity⟩
  exact (GeneralBorrowLoop.list_invariant _ scan property step _ initial).2.2

def Before (tree : BorrowTree) (protections : ProtectedTags) (root earlier : UniIndex) (location : LocationTree) : Prop :=
  LocationCompatible tree protections root location ∧
  GeneralBorrowLocationSifaConsistency.Profile tree location protections ∧
  ∃ state,tree.locationStateAt location earlier = some state ∧ state.permission = .ReservedFrz false
/-- Actual bounded leading Read conflicts earlier held reservations in the stored range, with the broader initial compatibility. -/
theorem root_conflict (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (root earlier : UniIndex)
    (rootNode earlierNode : TreeNode) (offset len : UInt64)
    (fits : tree.nodes.data.size ≤ 4294967296) (depth : ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (covered : GeneralBorrowGraph.RootsCover tree)
    (roots : tree.roots = #[root]) (tagPresent : tree.indexOfTag tag = some root)
    (rootPresent : tree.nodeAt root = some rootNode) (parentless : rootNode.parent = none)
    (earlierPresent : tree.nodeAt earlier = some earlierNode) (listed : earlier ∈ rootNode.children)
    (held : protections.contains earlierNode.tag = true) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (initial : Every (Before tree protections root earlier) tree.locations) :
    let result := tree.performNormalAccessRange tag (Size.ofBytes offset) (Size.ofBytes len) .Read protections .VisitChildrenOfAccessed
    result.status = .Completed ∧
      OwnedOn (At earlier (some (.ReservedFrz true))) offset (offset+len) result.tree.locations := by
  have sourceCompatible : Every (LocationCompatible tree protections root) tree.locations := by
    intro position valid
    exact (initial position valid).1
  have complete := access tree protections tag root root (Size.ofBytes offset) (Size.ofBytes len)
    .VisitChildrenOfAccessed depth children rootNode rootPresent roots covered tagPresent well sourceCompatible bounds
  refine ⟨complete,?_⟩
  apply GeneralBorrowRangeCallbackOutput.outputs tree protections tag root (Size.ofBytes offset) (Size.ofBytes len)
    .Read .VisitChildrenOfAccessed (At earlier (some (.ReservedFrz true))) tagPresent well bounds
  intro cursor valid
  have prepared := GeneralRangeMapSafety.iter_mut (Before tree protections root earlier) tree.locations
    (Size.ofBytes offset) (Size.ofBytes len) well initial bounds
  have here := prepared.every
  have segmentBound : cursor < (tree.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)).segments.size := valid
  have cursorBound : cursor < (tree.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)).positions.size := by rw [←prepared.lengths] at segmentBound;exact segmentBound
  obtain ⟨positionBound,selected⟩ := prepared.selected cursor cursorBound
  have before : Before tree protections root earlier (tree.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)).segments[cursor].data := by
    rw [selected];exact prepared.every _ positionBound
  obtain ⟨⟨⟨forest⟩,rootValid,compatible⟩,profile,state,stored,reservation⟩ := before
  let segment := (tree.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)).segments[cursor]
  have conflict := GeneralBorrowProtectedReadLocation.root_conflict tree segment.data protections root earlier rootNode earlierNode state
    fits depth children rootPresent parentless earlierPresent listed stored reservation held forest compatible profile
  have actual := GeneralBorrowProtectedReadSingleRoot.access_at tree segment.data protections root root .VisitChildrenOfAccessed segment.range
    forest rootValid compatible depth children rootNode rootPresent roots covered
  refine ⟨actual,?_⟩
  rw [GeneralBorrowProtectedReadSingleRoot.single_root_location tree segment.data protections root root .VisitChildrenOfAccessed segment.range
    forest rootValid compatible depth children rootNode rootPresent roots covered]
  obtain ⟨next,present,permission⟩ := conflict.2.2
  simp only [At,present,Option.map_some,permission]

end DuplicatePrefix.GeneralBorrowProtectedReadRange
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedReadRange.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected Read range dependency {dependency}"
