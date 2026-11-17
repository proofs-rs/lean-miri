import duplicate_prefix.GeneralBorrowFreshReadFrame
import duplicate_prefix.GeneralRangeMapOriginPrepare
namespace DuplicatePrefix.GeneralBorrowStructuralAccessGeometry
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Every outcome of the real ranged Read/Write preserves partition geometry.
Only preparation requires bounds; access failures and stopped prefixes retain
well-formedness and exact capacity because callbacks replace data, not ranges.
No ownership, successful access, tag presence or cache invariant is required. -/
theorem access (tree : BorrowTree) (provenance : ProvenanceExtra) (offset len : Size)
    (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode)
    (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat) :
    let result := tree.performBorrowAccessRange provenance offset len kind protections mode
    result.tree.locations.WellFormed ∧ result.tree.locations.size = tree.locations.size := by
  let prepared := tree.locations.iterMut offset len
  have good := (GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds).1
  unfold BorrowTree.performBorrowAccessRange
  cases provenance
  case' concrete tag =>
    cases lookup : tree.indexOfTag tag
    case none => simpa only [lookup,Option.isNone_none,↓reduceIte,Id.run,pure] using And.intro well (Eq.refl tree.locations.size)
    case' some index => simp only [lookup,Option.isNone_some,Bool.false_eq_true,↓reduceIte]
  case' wildcard => simp only
  all_goals
    simp only [Id.run,bind,pure,good.outcome]
    simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
    name_borrow_range_scan
    let property := fun state : DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus =>
      state.1.WellFormed ∧ state.1.size = tree.locations.size ∧ state.1.entries.size = prepared.state.entries.size
    have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
        property state → property (scan cursor state).value := by
      intro cursor member state maintained
      rcases state with ⟨current,visited,status⟩
      rcases maintained with ⟨currentWell,capacity,sizeEq⟩
      by_cases completed : status = .Completed
      · subst status
        have cursorBound : cursor < prepared.positions.size := by have := List.mem_range'_1.mp member;omega
        have segmentBound : cursor < prepared.segments.size := by rw [←good.lengths];exact cursorBound
        let position := prepared.positions[cursor]'cursorBound
        let segment := prepared.segments[cursor]'segmentBound
        obtain ⟨positionBound,selected⟩ := good.selected cursor cursorBound
        have currentBound : position < current.entries.size := by rw [sizeEq];exact positionBound
        have positionLookup : (tree.locations.iterMut offset len).positions[cursor]? = some position := Array.getElem?_eq_getElem cursorBound
        have segmentLookup : (tree.locations.iterMut offset len).segments[cursor]? = some segment := Array.getElem?_eq_getElem segmentBound
        simp only [scan,beq_self_eq_true,↓reduceIte,positionLookup,segmentLookup,setAtPos_success current position currentBound]
        split
        all_goals
          dsimp only [property,ForInStep.value]
          rw [setAtPos_exact current position currentBound]
          exact ⟨replaced_wellFormed current position currentBound _ currentWell,
            (replaced_size current position currentBound _).trans capacity,
            (replaced_length current position currentBound _).trans sizeEq⟩
      · simpa only [scan,beq_iff_eq,completed,Bool.false_eq_true,↓reduceIte,ForInStep.value,property] using
          And.intro currentWell (And.intro capacity sizeEq)
    have initial : property (prepared.state,#[],.Completed) :=
      ⟨good.wellFormed,congrArg Size.ofBytes good.capacity,rfl⟩
    have final := DuplicatePrefix.GeneralBorrowLoop.list_invariant _ scan property step _ initial
    exact ⟨final.1,final.2.1⟩
end DuplicatePrefix.GeneralBorrowStructuralAccessGeometry
