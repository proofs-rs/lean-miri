import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableReadClosed
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableReadPostMap
import duplicate_prefix.GeneralRangeMapOriginPrepare
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableReadRange
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralRangeMapState
open GeneralBorrowExposedScopedInactiveWritableReadData
open GeneralBorrowExposedScopedInactiveWritableReadPostMap
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

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

/-- Actual ranged concrete Read/Write across arbitrary well-formed partitions
and bounded subslices. Only the borrowed window supplies initial component
records; successful local operations, exact cache counters, range geometry and
kind-specific scoped postprofiles are derived. The selected root can occur at
any position, with arbitrary exposed nonleaf other components. -/
theorem access (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (anchor selected head : UniIndex) (tail : List UniIndex) (offset len : Size)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (support : Nat → Prop) (writable : Nat → Bool) (fits : tree.nodes.data.size ≤ 4294967296)
    (tagPresent : tree.indexOfTag tag = some anchor) (well : tree.locations.WellFormed)
    (sliceStart sliceStop : UInt64)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Data tree location protections anchor selected head tail support writable)) sliceStart sliceStop tree.locations)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : sliceStart.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes+len.bytes).toNat ≤ sliceStop.toNat) :
    let result := tree.performBorrowAccessRange (.concrete tag) offset len .Read protections .VisitChildrenOfAccessed
    result.status = .Completed ∧
      GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (Data result.tree location protections anchor selected head tail support writable)) sliceStart sliceStop result.tree.locations ∧
      result.tree.locations.WellFormed ∧ result.tree.locations.size = tree.locations.size := by
  dsimp only
  let predicate := fun location => Nonempty (Data tree location protections anchor selected head tail support writable)
  let dataPredicate := fun location => Nonempty (Data tree location protections anchor selected head tail support writable)
  have posts : GeneralRangeMapOrigins.OwnedOn predicate sliceStart sliceStop tree.locations := by
    intro position valid positive start stop
    obtain ⟨data⟩ := owned position valid positive start stop
    exact ⟨data⟩
  let prepared := tree.locations.iterMut offset len
  have preparedData := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have preparedGood := preparedData.1
  have preparedOwners := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    dataPredicate sliceStart sliceStop owned requestLower requestUpper
  have preparedPosts := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    predicate sliceStart sliceStop posts requestLower requestUpper
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
    obtain ⟨positionBound,segmentSelected⟩ := preparedGood.selected cursor cursorBound
    have localData : Nonempty (Data tree segment.data protections anchor selected head tail support writable) :=
      preparedOwners.2.2 cursor segmentBound
    obtain ⟨data⟩ := localData
    have accessResult := GeneralBorrowExposedScopedInactiveWritableReadClosed.access tree segment.data protections anchor selected head tail segment.range context support writable fits data
    have accessGood := accessResult.1
    let accessed := source_tree_access_at tree segment.data (some anchor) .Read protections .VisitChildrenOfAccessed segment.range
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
    ⟨rfl,rfl,preparedPosts.2.1,preparedGood.wellFormed,congrArg Size.ofBytes preparedGood.capacity⟩
  have final := GeneralBorrowLoop.list_invariant _ scan property step _ start
  refine ⟨final.1,?_,final.2.2.2.1,final.2.2.2.2⟩
  intro index valid positive beforeUpper afterLower
  rw [post_map]
  exact final.2.2.1 index valid positive beforeUpper afterLower

end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableReadRange
