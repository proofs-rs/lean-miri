import duplicate_prefix.GeneralBorrowFreshActiveWithin
import duplicate_prefix.GeneralBorrowProtectedSiblingPartialForeign
import duplicate_prefix.GeneralBorrowProtectedReadableStage
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingPartialActive
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshActiveWithin
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem replace_write (map : DedupRangeMap LocationTree) (position : Nat)
    (valid : position < map.entries.size) (location : LocationTree) (anchor : UniIndex) (lower upper : UInt64)
    (active : Profile map anchor .Write lower upper)
    (preserved : ∀ (point : UInt64), map.entries[position].range.start.toNat ≤ point.toNat → point.toNat < map.entries[position].range.stop.toNat →
      ∀ state,location.perms.get anchor = some state → state.accessed = true → ∀ kind,state.permission.associatedAccess = some kind →
        lower.toNat ≤ point.toNat ∧ point.toNat < upper.toNat) :
    Profile (replaced map position valid location) anchor .Write lower upper := by
  intro point value atPoint state stored accessed kind associated
  obtain ⟨query,bounded,startPoint,pointStop,dataEq⟩ := atPoint
  have oldBound : query < map.entries.size := by simpa only [replaced_length] using bounded
  rw [replaced_range map position valid location query oldBound] at startPoint pointStop
  by_cases same : position = query
  · subst query
    have sameData : location = value := by simpa only [replaced,Array.getElem_set_self] using dataEq
    rw [←sameData] at stored
    have bounds := preserved point startPoint pointStop state stored accessed kind associated
    exact ⟨bounds.1,bounds.2,by intro h;cases h⟩
  · have dataSame : (replaced map position valid location).entries[query].data = map.entries[query].data := by simp [replaced,Array.getElem_set,same]
    rw [dataSame] at dataEq
    exact active point value ⟨query,oldBound,startPoint,pointStop,dataEq⟩ state stored accessed kind associated

/-- The actual constructor-leading Read retains an earlier direct sibling's
bytewise activity interval for arbitrary partial-window overlap. No containment
between requested windows or successful-access premise is required. -/
theorem read (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (roots : input.tree.roots = #[input.parent])
    (readable : Every (GeneralBorrowProtectedReadRelease.Profile input.tree protections) input.tree.locations)
    (anchor : UniIndex) (node : TreeNode) (present : input.tree.nodeAt anchor = some node) (parent : node.parent = some input.parent)
    (lower upper : UInt64) (active : ActiveWithin input.tree anchor .Write lower upper) :
    ActiveWithin (GeneralBorrowProtectedReadableStage.read input protections).tree anchor .Write lower upper := by
  let tree := input.tree
  let tag := input.parentTag
  let offset := Size.ofBytes input.offset
  let len := Size.ofBytes input.len
  let kind := AccessKind.Read
  let mode := ChildrenVisitMode.VisitChildrenOfAccessed
  have well := input.well
  have bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat := input.bounds
  change ActiveWithin (tree.performNormalAccessRange tag offset len kind protections mode).tree anchor .Write lower upper
  let prepared := tree.locations.iterMut offset len
  have preparedData := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have good := preparedData.1
  have preparedReadable := GeneralRangeMapSafety.iter_mut (GeneralBorrowProtectedReadRelease.Profile tree protections) tree.locations offset len well readable bounds
  have preparedActive := refines tree.locations prepared.state preparedData.2.1 anchor .Write lower upper active
  unfold BorrowTree.performNormalAccessRange BorrowTree.performBorrowAccessRange
  cases lookup : tree.indexOfTag tag with
  | none => have same : tree.indexOfTag tag = some input.parent := input.parentTagPresent;rw [lookup] at same;cases same
  | some source =>
    have sourceEq : source = input.parent := Option.some.inj (lookup.symm.trans input.parentTagPresent)
    subst source
    simp only [lookup,Option.isNone_some,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure,good.outcome]
    simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
    name_borrow_range_scan
    let property := fun state : DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus =>
      state.1.entries.map (·.range) = prepared.state.entries.map (·.range) ∧ Profile state.1 anchor .Write lower upper
    have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
        property state → property (scan cursor state).value := by
      intro cursor member state maintained
      rcases state with ⟨current,visited,status⟩
      rcases maintained with ⟨ranges,currentActive⟩
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
        let access := source_tree_access_at tree segment.data (some input.parent) kind protections mode segment.range
        let mutation := current.setAtPos position (source_access_location access)
        have afterRanges : mutation.state.entries.map (·.range) = prepared.state.entries.map (·.range) := by
          dsimp only [mutation]
          rw [setAtPos_exact current position currentBound,replaced_ranges]
          exact ranges
        have afterActive : Profile mutation.state anchor .Write lower upper := by
          dsimp only [mutation]
          rw [setAtPos_exact current position currentBound]
          apply replace_write current position currentBound _ anchor lower upper currentActive
          intro point startPoint pointStop state stored accessed accessKind associated
          by_cases inside : lower.toNat ≤ point.toNat ∧ point.toNat < upper.toNat
          · exact inside
          · have oldRange : prepared.state.entries[position].range = segment.range := (congrArg (fun entry : RangeMapSegment LocationTree => entry.range) selected).symm
            have oldData : prepared.state.entries[position].data = segment.data := (congrArg (fun entry : RangeMapSegment LocationTree => entry.data) selected).symm
            have atPoint : ValueAt prepared.state point segment.data := ⟨position,positionBound,by rw [oldRange,←rangeSame];exact startPoint,by rw [oldRange,←rangeSame];exact pointStop,oldData⟩
            have oldQuiet : GeneralBorrowProtectedSiblingForeignReadQuiet.LocationTyped segment.data anchor := by
              intro old oldStored
              by_cases cell : old.permission = .Cell
              · exact Or.inr cell
              · apply Or.inl
                by_cases notFalse : old.accessed = false
                · exact notFalse
                · have oldAccessed : old.accessed = true := by
                    cases flag : old.accessed with
                    | false => exact False.elim (notFalse flag)
                    | true => first | exact flag | rfl
                  have oldAssociated : ∃ accessKind,old.permission.associatedAccess = some accessKind := by
                    cases permission : old.permission <;> simp_all [Permission.associatedAccess]
                  obtain ⟨oldKind,oldAssociated⟩ := oldAssociated
                  have wasInside := preparedActive point segment.data atPoint old oldStored oldAccessed oldKind oldAssociated
                  exact False.elim (inside ⟨wasInside.1,wasInside.2.1⟩)
            have segmentReadable : GeneralBorrowProtectedReadRelease.Profile tree protections segment.data := by
              have property := preparedReadable.every position positionBound
              rw [←selected] at property
              exact property
            obtain ⟨⟨forest⟩,data⟩ := segmentReadable
            have newQuiet := GeneralBorrowProtectedSiblingPartialForeign.location input protections segment.data segment.range roots anchor node present parent forest data oldQuiet
            rcases newQuiet state stored with inactive | cell
            · rw [accessed] at inactive;cases inactive
            · rw [cell,Permission.associatedAccess] at associated;cases associated
        have positionLookup : (tree.locations.iterMut offset len).positions[cursor]? = some position := Array.getElem?_eq_getElem cursorBound
        have segmentLookup : (tree.locations.iterMut offset len).segments[cursor]? = some segment := Array.getElem?_eq_getElem segmentBound
        dsimp only [mutation,access] at afterRanges afterActive
        cases failure : source_access_status access
        all_goals dsimp only [access] at failure
        all_goals simpa only [scan,beq_self_eq_true,↓reduceIte,positionLookup,segmentLookup,
            setAtPos_success current position currentBound,failure,property,ForInStep.value]
            using And.intro afterRanges afterActive
      · simpa only [scan,beq_iff_eq,completed,Bool.false_eq_true,↓reduceIte,ForInStep.value,property] using And.intro ranges currentActive
    have initial : property (prepared.state,#[],.Completed) := ⟨rfl,preparedActive⟩
    have final := DuplicatePrefix.GeneralBorrowLoop.list_invariant _ scan property step (prepared.state,#[],.Completed) initial
    exact final.2
end DuplicatePrefix.GeneralBorrowProtectedSiblingPartialActive
