import duplicate_prefix.S03EmptyPopFactsTreeAccess
import duplicate_prefix.GeneralRangeMapOriginPrepare

namespace DuplicatePrefix.S03EmptyPopFactsRange
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection BorrowRangeAccess GeneralBorrowExposureCardinality GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- The real ranged concrete Read/Write preserves an inactive empty leaf,
including all secondary physical-root callbacks and all error prefixes. The
normal permissions are supplied by the current positive source capability. -/
theorem concrete (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag) (source selected query : UniIndex) (maximum : Option BorTag)
    (offset len : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags
      (some source) (some selected) maximum offset len)
    (tagged : tree.indexOfTag tag = some source)
    (node : TreeNode) (present : tree.nodeAt query = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (different : query ≠ source)
    (inactive : Every (fun location => (GeneralBorrowWildcardVirtualLeaf.effective location query node).accessed = false) tree.locations)
    (kind : AccessKind) (mode : ChildrenVisitMode) :
    Every (fun location => (GeneralBorrowWildcardVirtualLeaf.effective location query node).accessed = false)
      (tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len)
        kind global.protectedTags mode).tree.locations := by
  let predicate := fun location => (GeneralBorrowWildcardVirtualLeaf.effective location query node).accessed = false
  let prepared := tree.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)
  have preparedGood := GeneralRangeMapSafety.iter_mut predicate tree.locations (Size.ofBytes offset) (Size.ofBytes len) runtime.formed.well inactive positive.bounds
  have preparedOwners := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations (Size.ofBytes offset) (Size.ofBytes len) runtime.formed.well positive.bounds
    (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Row tree location global.protectedTags
      (some source) (some selected) maximum)) offset (offset+len) positive.rows (Nat.le_refl _) (Nat.le_refl _)
  have preparedCoherent := GeneralRangeMapSafety.iter_mut
    (fun location => LocationCoherent tree location global.protectedTags) tree.locations (Size.ofBytes offset) (Size.ofBytes len) runtime.formed.well runtime.coherent positive.bounds
  obtain ⟨sourceNode,sourcePresent⟩ := positive.sourcePresent source rfl
  unfold BorrowTree.performBorrowAccessRange
  simp only [tagged,Option.isNone_some,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure,preparedGood.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  let property := fun (state : DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus) =>
    state.1.entries.size = prepared.state.entries.size ∧ Every predicate state.1
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
      property state → property (scan cursor state).value := by
    intro cursor member state maintained
    rcases state with ⟨current,visited,status⟩
    have sizeEq := maintained.1
    by_cases completed : status = .Completed
    · subst status
      have cursorBound : cursor < prepared.positions.size := by have bound := List.mem_range'_1.mp member;omega
      have segmentBound : cursor < prepared.segments.size := by rw [←preparedGood.lengths];exact cursorBound
      let position := prepared.positions[cursor]'cursorBound
      let segment := prepared.segments[cursor]'segmentBound
      obtain ⟨positionBound,selectedPosition⟩ := preparedGood.selected cursor cursorBound
      have currentBound : position < current.entries.size := by rw [sizeEq];exact positionBound
      have segmentInactive : predicate segment.data := by
        rw [show segment = prepared.state.entries[position]'positionBound from selectedPosition]
        exact preparedGood.every position positionBound
      have segmentCoherent : LocationCoherent tree segment.data global.protectedTags := by
        rw [show segment = prepared.state.entries[position]'positionBound from selectedPosition]
        exact preparedCoherent.every position positionBound
      obtain ⟨row⟩ := preparedOwners.2.2 cursor segmentBound
      obtain ⟨normal⟩ := row.normal source rfl
      have preserved := (S03EmptyPopFactsTreeAccess.concrete tree runtime.formed.toGraphState segment.data global.protectedTags
        query source node sourceNode present sourcePresent leaf hidden different normal segmentCoherent kind mode segment.range segmentInactive).1
      let access := source_tree_access_at tree segment.data (some source) kind global.protectedTags mode segment.range
      let mutation := current.setAtPos position (source_access_location access)
      have nextSize : mutation.state.entries.size = prepared.state.entries.size :=
        (setAtPos_length current position currentBound _).trans sizeEq
      have nextEvery : Every predicate mutation.state := by
        dsimp only [mutation]
        rw [setAtPos_exact current position currentBound]
        exact replaced_every predicate current position currentBound _ maintained.2 preserved
      have positionLookup : (tree.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)).positions[cursor]? = some position := Array.getElem?_eq_getElem cursorBound
      have segmentLookup : (tree.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)).segments[cursor]? = some segment := Array.getElem?_eq_getElem segmentBound
      cases failure : source_access_status access
      all_goals dsimp only [access] at failure
      all_goals simpa only [scan,beq_self_eq_true,↓reduceIte,positionLookup,segmentLookup,setAtPos_success current position currentBound,
          failure,property,ForInStep.value] using And.intro nextSize nextEvery
    · simpa only [scan,beq_iff_eq,completed,Bool.false_eq_true,↓reduceIte,ForInStep.value,property] using maintained
  have initial : property (prepared.state,#[],.Completed) := ⟨rfl,preparedGood.every⟩
  exact (GeneralBorrowLoop.list_invariant _ scan property step _ initial).2

/-- The preserved stored inactive bit discharges the actual zero-tag release
scan's Quiescent condition after the one-byte return Write. -/
theorem quiescent (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag) (source selected query : UniIndex) (maximum : Option BorTag)
    (offset : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags
      (some source) (some selected) maximum offset 1)
    (tagged : tree.indexOfTag tag = some source)
    (node : TreeNode) (present : tree.nodeAt query = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (different : query ≠ source)
    (inactive : Every (fun location => (GeneralBorrowWildcardVirtualLeaf.effective location query node).accessed = false) tree.locations) :
    S04ReturnReleaseInactive.Quiescent
      (tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes 1)
        .Write global.protectedTags .VisitChildrenOfAccessed).tree query := by
  have kept := concrete tree global runtime tag source selected query maximum offset 1 positive tagged node present leaf hidden different inactive .Write .VisitChildrenOfAccessed
  intro position valid state stored
  left
  have here := kept position valid
  simpa only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_some] using here

end DuplicatePrefix.S03EmptyPopFactsRange
