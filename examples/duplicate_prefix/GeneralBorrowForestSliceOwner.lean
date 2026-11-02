import duplicate_prefix.GeneralBorrowForestModeOwner
import duplicate_prefix.GeneralRangeMapOriginPrepare

namespace DuplicatePrefix.GeneralBorrowForestSliceOwner
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralRangeMapState
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowForestModeAccess (LocationData)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Slice-local initial graph/permission records for an operation and the
ownership strength retained by that operation. Region exclusion is initial
forest data, not an operation-success assumption. -/
structure InputLocation (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (extras : List UniIndex) (kind ownerKind : AccessKind) (mode : ChildrenVisitMode) where
  data : LocationData tree location protections anchor primary extras kind mode
  owner : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat ownerKind
  foreignGraph : ∀ query, data.region.support query →
    query.toNat ∉ (source_normal_projection tree location protections).topology.ancestorPath anchor.toNat

private theorem replaced_owned_on (predicate : α → Prop) (lower upper : UInt64)
    (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size) (data : α)
    (owned : GeneralRangeMapOrigins.OwnedOn predicate lower upper map) (newOwned : predicate data) :
    GeneralRangeMapOrigins.OwnedOn predicate lower upper (replaced map position valid data) := by
  intro index bounded positive beforeUpper afterLower
  have oldBound : index < map.entries.size := by simpa only [replaced_length] using bounded
  rw [replaced_range map position valid data index oldBound] at beforeUpper afterLower
  by_cases same : position = index
  · subst index
    simpa [replaced] using newOwned
  · have previous := owned index oldBound positive beforeUpper afterLower
    simpa [replaced,Array.getElem_set,same] using previous

/-- Actual normal-plus-extra-subtree ranged access preserves the primary
anchor's ownership over its entire borrowed window, without ownership outside
that window. In particular mutable ownership is retained across a Read. -/
theorem access (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (anchor primary : UniIndex) (extras : List UniIndex) (offset len : Size) (kind ownerKind : AccessKind) (mode : ChildrenVisitMode)
    (context : Context tree anchor primary extras)
    (tagPresent : tree.indexOfTag tag = some anchor) (well : tree.locations.WellFormed)
    (fits : tree.nodes.data.size ≤ 4294967296) (allowed : ownerKind = .Read → kind = .Read)
    (sliceStart sliceStop : UInt64)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (InputLocation tree location protections anchor primary extras kind ownerKind mode)) sliceStart sliceStop tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : sliceStart.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes+len.bytes).toNat ≤ sliceStop.toNat) :
    let result := tree.performBorrowAccessRange (.concrete tag) offset len kind protections mode
    result.status = .Completed ∧
    GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned result.tree protections anchor ownerKind) sliceStart sliceStop result.tree.locations ∧
    result.tree.locations.WellFormed ∧ result.tree.locations.size = tree.locations.size := by
  dsimp only
  let inputPredicate := fun location => Nonempty (InputLocation tree location protections anchor primary extras kind ownerKind mode)
  let predicate := GeneralBorrowRange.LocationOwned tree protections anchor ownerKind
  have initialOwners : GeneralRangeMapOrigins.OwnedOn predicate sliceStart sliceStop tree.locations := by
    intro index valid positive beforeUpper afterLower
    obtain ⟨data⟩ := owned index valid positive beforeUpper afterLower
    exact ⟨⟨data.data.forest⟩,data.owner⟩
  let prepared := tree.locations.iterMut offset len
  have preparedData := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have preparedGood := preparedData.1
  have preparedInputs := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    inputPredicate sliceStart sliceStop owned requestLower requestUpper
  have preparedOwners := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    predicate sliceStart sliceStop initialOwners requestLower requestUpper
  unfold BorrowTree.performBorrowAccessRange
  simp only [tagPresent,Option.isNone_some,Bool.false_eq_true,↓reduceIte]
  simp only [Id.run,bind,pure,preparedGood.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  let property := fun state : DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus =>
    state.2.2 = .Completed ∧ state.1.entries.size = prepared.state.entries.size ∧
      GeneralRangeMapOrigins.OwnedOn predicate sliceStart sliceStop state.1 ∧
      state.1.WellFormed ∧ state.1.size = tree.locations.size
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
      property state → property (scan cursor state).value := by
    intro cursor member state good
    rcases state with ⟨current,visited,status⟩
    rcases good with ⟨statusEq,sizeEq,currentOwners,wellFormed,capacity⟩
    dsimp only at statusEq sizeEq
    subst status
    have cursorBound : cursor < prepared.positions.size := by
      have bounded := List.mem_range'_1.mp member
      simpa using bounded.2
    have segmentBound : cursor < prepared.segments.size := by rw [←preparedGood.lengths];exact cursorBound
    let position := prepared.positions[cursor]'cursorBound
    let segment := prepared.segments[cursor]'segmentBound
    obtain ⟨positionBound,selected⟩ := preparedGood.selected cursor cursorBound
    have localData : Nonempty (InputLocation tree segment.data protections anchor primary extras kind ownerKind mode) :=
      preparedInputs.2.2 cursor segmentBound
    obtain ⟨data⟩ := localData
    have accessResult := GeneralBorrowForestModeOwner.access_owned tree segment.data protections anchor primary extras kind ownerKind mode segment.range
      context data.data fits allowed data.owner data.foreignGraph
    have accessGood := accessResult.1
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
    refine ⟨rfl,(setAtPos_length current position currentBound _).trans sizeEq,?_,?_,?_⟩
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact replaced_owned_on predicate sliceStart sliceStop current position currentBound _ currentOwners accessResult.2
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact replaced_wellFormed current position currentBound _ wellFormed
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact (replaced_size current position currentBound _).trans capacity
  have start : property (prepared.state,#[],.Completed) :=
    ⟨rfl,rfl,preparedOwners.2.1,preparedGood.wellFormed,congrArg Size.ofBytes preparedGood.capacity⟩
  have final := GeneralBorrowLoop.list_invariant _ scan property step _ start
  exact ⟨final.1,final.2.2.1,final.2.2.2.1,final.2.2.2.2⟩

end DuplicatePrefix.GeneralBorrowForestSliceOwner
