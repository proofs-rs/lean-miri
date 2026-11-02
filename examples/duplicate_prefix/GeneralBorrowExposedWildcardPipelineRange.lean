import duplicate_prefix.GeneralBorrowExposedWildcardReadConstructorNext
import duplicate_prefix.GeneralBorrowFreshRangeFrame
namespace DuplicatePrefix.GeneralBorrowExposedWildcardPipelineRange
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.RangeMapNonempty DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowWildcardLeaf DuplicatePrefix.GeneralBorrowExposureCardinality
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem dispatch (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (anchor : UniIndex)
    (offset len : Size) (kind : AccessKind) (mode : ChildrenVisitMode)
    (tagPresent : tree.indexOfTag tag = some anchor) (well : tree.locations.WellFormed) (sliceStart sliceStop : UInt64)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => ∀ range : ByteRange, source_access_status (source_tree_access_at tree location (some anchor) kind protections mode range) = none)
      sliceStart sliceStop tree.locations)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : sliceStart.toNat ≤ offset.bytes.toNat) (requestUpper : (offset.bytes+len.bytes).toNat ≤ sliceStop.toNat) :
    let result := tree.performBorrowAccessRange (.concrete tag) offset len kind protections mode
    result.status = .Completed ∧ result.tree.locations.WellFormed ∧ result.tree.locations.size = tree.locations.size := by
  dsimp only
  let predicate := fun location => ∀ range : ByteRange, source_access_status (source_tree_access_at tree location (some anchor) kind protections mode range) = none
  let prepared := tree.locations.iterMut offset len
  have preparedData := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have preparedGood := preparedData.1
  have preparedOwners := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    predicate sliceStart sliceStop owned requestLower requestUpper
  unfold BorrowTree.performBorrowAccessRange
  simp only [tagPresent,Option.isNone_some,Bool.false_eq_true,↓reduceIte]
  simp only [Id.run,bind,pure,preparedGood.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  let property := fun state : DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus =>
    state.2.2 = .Completed ∧ state.1.entries.size = prepared.state.entries.size ∧
      state.1.WellFormed ∧ state.1.size = tree.locations.size
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
      property state → property (scan cursor state).value := by
    intro cursor member state good
    rcases state with ⟨current,visited,status⟩
    rcases good with ⟨statusEq,sizeEq,wellFormed,capacity⟩
    dsimp only at statusEq sizeEq
    subst status
    have cursorBound : cursor < prepared.positions.size := by
      have bounded := List.mem_range'_1.mp member
      simpa using bounded.2
    have segmentBound : cursor < prepared.segments.size := by rw [←preparedGood.lengths];exact cursorBound
    let position := prepared.positions[cursor]'cursorBound
    let segment := prepared.segments[cursor]'segmentBound
    obtain ⟨positionBound,selected⟩ := preparedGood.selected cursor cursorBound
    have localData : predicate segment.data := preparedOwners.2.2 cursor segmentBound
    have accessGood := localData segment.range
    let accessed := source_tree_access_at tree segment.data (some anchor) kind protections mode segment.range
    let mutation := current.setAtPos position (source_access_location accessed)
    have currentBound : position < current.entries.size := by rw [sizeEq];exact positionBound
    have positionLookup : (tree.locations.iterMut offset len).positions[cursor]? = some position := Array.getElem?_eq_getElem cursorBound
    have segmentLookup : (tree.locations.iterMut offset len).segments[cursor]? = some segment := Array.getElem?_eq_getElem segmentBound
    have actual : scan cursor (current,visited,.Completed) =
        .yield (mutation.state,visited.push ⟨segment.range,source_access_normal accessed⟩,.Completed) := by
      simp only [scan,beq_self_eq_true,↓reduceIte,positionLookup,segmentLookup,
        setAtPos_success current position currentBound,accessGood]
      rfl
    rw [actual]
    refine ⟨rfl,(setAtPos_length current position currentBound _).trans sizeEq,?_,?_⟩
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact replaced_wellFormed current position currentBound _ wellFormed
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact (replaced_size current position currentBound _).trans capacity
  have start : property (prepared.state,#[],.Completed) :=
    ⟨rfl,rfl,preparedGood.wellFormed,congrArg Size.ofBytes preparedGood.capacity⟩
  have final := GeneralBorrowLoop.list_invariant _ scan property step _ start
  exact ⟨final.1,final.2.2.1,final.2.2.2⟩
/-- The real ranged wildcard Read, protected wildcard root constructor, and
subsequent ranged concrete Read all complete from initial resources. -/
theorem append (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (head : UniIndex) (headNode : TreeNode) (extras : List UniIndex) (nodes : UniIndex → TreeNode)
    (states : UniIndex → LocationState) (tag : BorTag) (capacity : UInt64) (nonzero : capacity ≠ 0)
    (locations : tree.locations = homogeneous capacity location)
    (roots : tree.roots = (head::extras).toArray)
    (headPresent : tree.nodes.get head = some headNode) (headLeaf : headNode.children = #[])
    (headExposed : headNode.isExposed = true) (headStored : location.perms.get head = some unique)
    (headBound : headNode.tag.value ≤ tag.value)
    (data : ∀ root ∈ extras, tree.nodes.get root = some (nodes root) ∧ (nodes root).children = #[] ∧
      (nodes root).isExposed = true ∧ (nodes root).tag.value ≤ tag.value ∧
      location.perms.get root = some (states root) ∧ supports (effective location protections root (nodes root)) .Read = true)
    (coherent : LocationCoherent tree location protections)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (noFree : tree.tagMapping.deassigned.back? = none)
    (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size) (short : tree.nodes.size+1 < 65536) :
    let read := tree.performBorrowAccessRange .wildcard Size.ZERO (Size.ofBytes capacity) .Read protections .VisitChildrenOfAccessed
    let inserted := read.tree.newChild Size.ZERO .wildcard tag
      (DedupRangeMap.new (Size.ofBytes capacity) ⟨.ReservedFrz false,true,.None⟩) (.ReservedFrz false) true
    let next := inserted.tree.performBorrowAccessRange (.concrete tag) Size.ZERO (Size.ofBytes capacity) .Read protections .VisitChildrenOfAccessed
    read.status = .Completed ∧ inserted.outcome = .ok () ∧ next.status = .Completed ∧ next.tree.locations.WellFormed := by
  have stages := GeneralBorrowExposedWildcardReadConstructorNext.append tree location protections depth head headNode extras nodes states tag capacity nonzero
    locations roots headPresent headLeaf headExposed headStored headBound data coherent fresh noFree aligned short
  have read := GeneralBorrowExposedWildcardStoredRead.ranged tree location protections head headNode extras nodes states capacity nonzero
    locations roots headPresent headLeaf headExposed headStored coherent (by omega)
    (fun root member => ⟨(data root member).1,(data root member).2.1,(data root member).2.2.1,
      (data root member).2.2.2.2.1,(data root member).2.2.2.2.2⟩)
  have well : tree.locations.WellFormed := by rw [locations];simp [homogeneous,DedupRangeMap.WellFormed,UInt64.pos_iff_ne_zero.mpr nonzero]
  have bounds : (0 : UInt64).toNat+capacity.toNat ≤ tree.locations.size.bytes.toNat := by
    rw [locations];simp [homogeneous,DedupRangeMap.size,Size.ofBytes]
  have fits : tree.tagMapping.mapping.size ≤ 4294967295 := by rw [aligned];change tree.nodes.data.size+1 < 65536 at short;omega
  have ctor := GeneralBorrowPositiveWildcardConstructor.append tree tag fresh noFree fits
    (.ReservedFrz false) .None ⟨.ReservedFrz false,true,.None⟩ true rfl rfl rfl rfl rfl 0 capacity nonzero well bounds
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  let mapping : UniKeyMap BorTag := ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned⟩
  let after := GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag (.ReservedFrz false) .None
    ⟨.ReservedFrz false,true,.None⟩ 0 capacity
  have mapFrame := GeneralBorrowFreshRangeFrame.modifyRange_frame tree.locations (Size.ofBytes 0) (Size.ofBytes capacity)
    (fun _ location => {location with perms := location.perms.insert index ⟨.ReservedFrz false,true,.None⟩}) well bounds
  have nextWell : after.locations.WellFormed := mapFrame.1
  have nextBounds : Size.ZERO.bytes.toNat+(Size.ofBytes capacity).bytes.toNat ≤ after.locations.size.bytes.toNat := by
    change (0 : UInt64).toNat+capacity.toNat ≤ _
    have capacityEq : after.locations.size.bytes = tree.locations.size.bytes := mapFrame.2
    rw [capacityEq]
    exact bounds
  have tagPresent : after.indexOfTag tag = some index := GeneralBorrowTagMap.pushed_get_new tree.tagMapping tag fresh index _
  dsimp only at stages ⊢
  rw [read.2] at stages ⊢
  have zero : Size.ZERO = Size.ofBytes 0 := rfl
  rw [zero,ctor] at stages ⊢
  have localGood : GeneralRangeMapOrigins.OwnedOn
      (fun location => ∀ range : ByteRange, source_access_status (source_tree_access_at after location (some index) .Read protections .VisitChildrenOfAccessed range) = none)
      0 capacity after.locations := by
    intro position valid positive start stop range
    exact (stages.2.2 position valid positive start stop range).1
  have final := dispatch after protections tag index (Size.ofBytes 0) (Size.ofBytes capacity) .Read .VisitChildrenOfAccessed
    tagPresent nextWell 0 capacity localGood nextBounds (Nat.le_refl _) (by change ((0 : UInt64)+capacity).toNat ≤ capacity.toNat;rw [UInt64.zero_add];exact Nat.le_refl _)
  exact ⟨read.1,rfl,final.1,final.2.1⟩
end DuplicatePrefix.GeneralBorrowExposedWildcardPipelineRange
