import duplicate_prefix.GeneralBorrowFreshFrozenFormation
namespace DuplicatePrefix.GeneralBorrowFreshActiveWithinRead
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshActiveWithin
open DuplicatePrefix.GeneralBorrowFreshFrozenTyping DuplicatePrefix.GeneralBorrowFreshFrozenFormation
open DuplicatePrefix.GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem replace_read (map : DedupRangeMap LocationTree) (position : Nat)
    (valid : position < map.entries.size) (location : LocationTree) (anchor : UniIndex) (lower upper : UInt64)
    (active : Profile map anchor .Read lower upper) (typed : LocationTyped location anchor)
    (inside : lower.toNat ≤ map.entries[position].range.start.toNat ∧ map.entries[position].range.stop.toNat ≤ upper.toNat) :
    Profile (replaced map position valid location) anchor .Read lower upper := by
  intro point value atPoint state stored accessed kind associated
  obtain ⟨query,bounded,startPoint,pointStop,dataEq⟩ := atPoint
  have oldBound : query < map.entries.size := by simpa only [replaced_length] using bounded
  rw [replaced_range map position valid location query oldBound] at startPoint pointStop
  by_cases same : position = query
  · subst query
    have valueEq : value = location := by simpa only [replaced,Array.getElem_set_self] using dataEq.symm
    have newStored : location.perms.get anchor = some state := by simpa only [valueEq] using stored
    exact ⟨Nat.le_trans inside.1 startPoint,Nat.lt_of_lt_of_le pointStop inside.2,
      fun _ => associated_read state (typed state newStored) kind associated⟩
  · have dataSame : (replaced map position valid location).entries[query].data = map.entries[query].data := by
      simp [replaced,Array.getElem_set,same]
    rw [dataSame] at dataEq
    exact active point value ⟨query,oldBound,startPoint,pointStop,dataEq⟩ state stored accessed kind associated

/-- Frozen/Disabled stored typing and the strong pointwise profile are retained
by an actual Read. Permissions are needed only on the requested source slice;
no successful access is supplied as an input assumption. -/
theorem normal (tree : BorrowTree) (tag : BorTag) (source root anchor : UniIndex)
    (offset len : Size) (protections : ProtectedTags) (mode : ChildrenVisitMode) (lower upper : UInt64)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (sourceNode : TreeNode) (sourcePresent : tree.nodeAt source = some sourceNode)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (tagPresent : tree.indexOfTag tag = some source)
    (well : tree.locations.WellFormed) (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : lower.toNat ≤ offset.bytes.toNat) (requestUpper : (offset.bytes+len.bytes).toNat ≤ upper.toNat)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections source .Read) lower upper tree.locations)
    (typed : TreeTyped tree anchor) (active : ActiveWithin tree anchor .Read lower upper) :
    let result := (tree.performNormalAccessRange tag offset len .Read protections mode).tree
    ActiveWithin result anchor .Read lower upper ∧ TreeTyped result anchor := by
  let prepared := tree.locations.iterMut offset len
  have preparedData := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have good := preparedData.1
  have preparedActive := refines tree.locations prepared.state preparedData.2.1 anchor .Read lower upper active
  have preparedTyped := GeneralRangeMapSafety.iter_mut (fun location => LocationTyped location anchor) tree.locations offset len well typed.2 bounds
  have preparedOwners := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    (GeneralBorrowRange.LocationOwned tree protections source .Read) lower upper owned requestLower requestUpper
  unfold BorrowTree.performNormalAccessRange BorrowTree.performBorrowAccessRange
  simp only [tagPresent,Option.isNone_some,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure,good.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  let property := fun state : DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus =>
    state.1.entries.map (·.range) = prepared.state.entries.map (·.range) ∧ Profile state.1 anchor .Read lower upper ∧ Every (fun location => LocationTyped location anchor) state.1
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
      property state → property (scan cursor state).value := by
    intro cursor member state maintained
    rcases state with ⟨current,visited,status⟩
    rcases maintained with ⟨ranges,currentActive,currentTyped⟩
    by_cases completed : status = .Completed
    · subst status
      have sizeEq : current.entries.size = prepared.state.entries.size := by
        have known := congrArg Array.size ranges
        simpa only [Array.size_map] using known
      have cursorBound : cursor < prepared.positions.size := by have := List.mem_range'_1.mp member;omega
      have segmentBound : cursor < prepared.segments.size := by rw [←good.lengths];exact cursorBound
      let position := prepared.positions[cursor]'cursorBound
      let segment := prepared.segments[cursor]'segmentBound
      obtain ⟨positionBound,selected⟩ := good.selected cursor cursorBound
      have currentBound : position < current.entries.size := by rw [sizeEq];exact positionBound
      have rangeSame : current.entries[position].range = segment.range := by
        have known := congrArg (fun rows => rows[position]?) ranges
        simp only [Array.getElem?_map,
          Array.getElem?_eq_getElem (xs := current.entries) (i := position) currentBound,
          Array.getElem?_eq_getElem (xs := prepared.state.entries) (i := position) positionBound,
          Option.map_some,Option.some.injEq] at known
        have selectedRange : prepared.state.entries[position].range = segment.range :=
          (congrArg (fun entry : RangeMapSegment LocationTree => entry.range) selected).symm
        exact known.trans selectedRange
      have selectedWithin := preparedData.2.2 cursor segmentBound
      change offset.bytes.toNat ≤ segment.range.start.toNat ∧ segment.range.stop.toNat ≤ (offset.bytes+len.bytes).toNat at selectedWithin
      have inside : lower.toNat ≤ current.entries[position].range.start.toNat ∧ current.entries[position].range.stop.toNat ≤ upper.toNat := by
        rw [rangeSame]
        exact ⟨Nat.le_trans requestLower selectedWithin.1,Nat.le_trans selectedWithin.2 requestUpper⟩
      let access := source_tree_access_at tree segment.data (some source) AccessKind.Read protections mode segment.range
      have accessTyped : LocationTyped (source_access_location access) anchor := by
        have selectedOwner := preparedOwners.2.2 cursor segmentBound
        obtain ⟨⟨forest⟩,owner⟩ := selectedOwner
        dsimp only [access]
        rw [GeneralBorrowRangePreserves.single_root_location tree segment.data protections source root .Read mode segment.range
          forest owner depth children sourceNode sourcePresent roots covered]
        apply GeneralBorrowFreshFrozenTyping.normal tree segment.data protections source anchor mode _ typed.1
        rw [show segment = prepared.state.entries[position]'positionBound from selected]
        exact preparedTyped.every position positionBound
      let mutation := current.setAtPos position (source_access_location access)
      have afterRanges : mutation.state.entries.map (·.range) = prepared.state.entries.map (·.range) := by
        dsimp only [mutation]
        rw [setAtPos_exact current position currentBound,replaced_ranges]
        exact ranges
      have afterActive : Profile mutation.state anchor .Read lower upper := by
        dsimp only [mutation]
        rw [setAtPos_exact current position currentBound]
        exact replace_read current position currentBound _ anchor lower upper currentActive accessTyped inside
      have afterTyped : Every (fun location => LocationTyped location anchor) mutation.state := by
        dsimp only [mutation]
        rw [setAtPos_exact current position currentBound]
        exact replaced_every _ current position currentBound _ currentTyped accessTyped
      have positionLookup : (tree.locations.iterMut offset len).positions[cursor]? = some position := Array.getElem?_eq_getElem cursorBound
      have segmentLookup : (tree.locations.iterMut offset len).segments[cursor]? = some segment := Array.getElem?_eq_getElem segmentBound
      dsimp only [mutation,access] at afterRanges afterActive afterTyped
      cases failure : source_access_status access
      all_goals dsimp only [access] at failure
      all_goals simpa only [scan,beq_self_eq_true,↓reduceIte,positionLookup,segmentLookup,
          setAtPos_success current position currentBound,failure,property,ForInStep.value]
          using ⟨afterRanges,afterActive,afterTyped⟩
    · simpa only [scan,beq_iff_eq,completed,Bool.false_eq_true,↓reduceIte,ForInStep.value,property] using ⟨ranges,currentActive,currentTyped⟩
  have initial : property (prepared.state,#[],.Completed) := ⟨rfl,preparedActive,preparedTyped.every⟩
  have final := DuplicatePrefix.GeneralBorrowLoop.list_invariant _ scan property step (prepared.state,#[],.Completed) initial
  exact ⟨final.2.1,typed.1,final.2.2⟩
end DuplicatePrefix.GeneralBorrowFreshActiveWithinRead
