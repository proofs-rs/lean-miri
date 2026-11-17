import duplicate_prefix.GeneralBorrowReadRowAccess
import duplicate_prefix.GeneralBorrowSnapshotWildcardRangeRuntime
namespace DuplicatePrefix.GeneralBorrowConcreteRangeInvariant
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralRangeMapOrigins
open GeneralBorrowExposedConditionalRangeFrames
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Pure output interface for source-bound concrete range composition. -/
structure Contract (before : BorrowTree) (rowPred runtimePred : LocationTree → Prop)
    (frame : LocationTree → LocationTree → Prop) (lower upper : UInt64)
    (result : BorrowTree.BorrowTreeAccessResult) : Prop where
  completed : result.status = .Completed
  runtime : Every runtimePred result.tree.locations
  rows : OwnedOn rowPred lower upper result.tree.locations
  well : result.tree.locations.WellFormed
  capacity : result.tree.locations.size = before.locations.size
  frames : Origins frame before.locations result.tree.locations
  nodes : result.tree.nodes = before.nodes
  roots : result.tree.roots = before.roots
  tags : result.tree.tagMapping = before.tagMapping

/-- The actual result differs only in its physical location map. -/
theorem Contract.tree_eq {before : BorrowTree} {rowPred runtimePred : LocationTree → Prop}
    {frame : LocationTree → LocationTree → Prop} {lower upper : UInt64}
    {result : BorrowTree.BorrowTreeAccessResult}
    (contract : Contract before rowPred runtimePred frame lower upper result) :
    result.tree = {before with locations := result.tree.locations} := by
  have nodes := contract.nodes
  have roots := contract.roots
  have tags := contract.tags
  cases before
  cases result with
  | mk after visited status => cases after;simp_all

private abbrev State := DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus
private structure Good (tree : BorrowTree) (rowPred runtimePred : LocationTree → Prop)
    (frame : LocationTree → LocationTree → Prop) (lower upper : UInt64)
    (prepared : DedupRangeMap LocationTree) (state : State) : Prop where
  completed : state.2.2 = .Completed
  length : state.1.entries.size = prepared.entries.size
  runtime : Every runtimePred state.1
  rows : OwnedOn rowPred lower upper state.1
  well : state.1.WellFormed
  capacity : state.1.size = tree.locations.size
  frames : Rows frame prepared state.1

/-- Generic actual concrete range iterator. Operational wrappers discharge its
local callback interface from raw capabilities; this is a composition lemma. -/
theorem access (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (anchor : UniIndex)
    (tagPresent : tree.indexOfTag tag = some anchor) (offset len : Size)
    (kind : AccessKind) (mode : ChildrenVisitMode)
    (rowPred runtimePred : LocationTree → Prop) (frame : LocationTree → LocationTree → Prop)
    (frameRefl : ∀ location, frame location location)
    (callback : ∀ location, rowPred location → runtimePred location → ∀ range,
      let accessed := source_tree_access_at tree location (some anchor) kind protections mode range
      source_access_status accessed = none ∧ rowPred (source_access_location accessed) ∧
        runtimePred (source_access_location accessed) ∧ frame location (source_access_location accessed))
    (lower upper : UInt64) (owned : OwnedOn rowPred lower upper tree.locations)
    (well : tree.locations.WellFormed) (all : Every runtimePred tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : lower.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes + len.bytes).toNat ≤ upper.toNat) :
    Contract tree rowPred runtimePred frame lower upper
      (tree.performBorrowAccessRange (.concrete tag) offset len kind protections mode) := by
  let prepared := tree.locations.iterMut offset len
  have preparedGood := GeneralRangeMapSafety.iter_mut
    runtimePred
    tree.locations offset len well all bounds
  have preparedOrigins := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have preparedOwners := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    rowPred lower upper owned requestLower requestUpper
  have rowsPrepared := preparedOwners.2.1
  unfold BorrowTree.performBorrowAccessRange
  simp only [tagPresent,Option.isNone_some,Bool.false_eq_true,↓reduceIte]
  simp only [Id.run,bind,pure,preparedGood.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
      Good tree rowPred runtimePred frame lower upper prepared.state state →
      Good tree rowPred runtimePred frame lower upper prepared.state (scan cursor state).value := by
    intro cursor member state good
    rcases state with ⟨current,visited,status⟩
    have completed := good.completed
    dsimp only at completed
    subst status
    have cursorBound : cursor < prepared.positions.size := by
      have bounded := List.mem_range'_1.mp member
      simpa using bounded.2
    have segmentBound : cursor < prepared.segments.size := by rw [←preparedGood.lengths];exact cursorBound
    let position := prepared.positions[cursor]'cursorBound
    let segment := prepared.segments[cursor]'segmentBound
    obtain ⟨positionBound,selectionEq⟩ := preparedGood.selected cursor cursorBound
    have rowHere : rowPred segment.data := preparedOwners.2.2 cursor segmentBound
    have runtimeHere : runtimePred segment.data := by
      have same : segment = prepared.state.entries[position]'positionBound := selectionEq
      rw [same]
      exact preparedGood.every position positionBound
    have callbackGood := callback segment.data rowHere runtimeHere segment.range
    let accessed := source_tree_access_at tree segment.data (some anchor) kind protections mode segment.range
    let mutation := current.setAtPos position (source_access_location accessed)
    have currentBound : position < current.entries.size := by rw [good.length];exact positionBound
    have positionLookup : (tree.locations.iterMut offset len).positions[cursor]? = some position := Array.getElem?_eq_getElem cursorBound
    have segmentLookup : (tree.locations.iterMut offset len).segments[cursor]? = some segment := Array.getElem?_eq_getElem segmentBound
    have actual : scan cursor (current,visited,.Completed) =
        .yield (mutation.state,visited.push ⟨segment.range,source_access_normal accessed⟩,.Completed) := by
      simp only [scan,beq_self_eq_true,↓reduceIte,positionLookup,segmentLookup,
        setAtPos_success current position currentBound,callbackGood.1]
      rfl
    rw [actual]
    refine ⟨rfl,(setAtPos_length current position currentBound _).trans good.length,?_,?_,?_,?_,?_⟩
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact replaced_every _ current position currentBound _ good.runtime callbackGood.2.2.1
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact replaced_owned_on _ lower upper current position currentBound _ good.rows callbackGood.2.1
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact replaced_wellFormed current position currentBound _ good.well
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact (replaced_size current position currentBound _).trans good.capacity
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      apply replaced_rows frame prepared.state current position currentBound _ good.frames positionBound
      have same : segment = prepared.state.entries[position]'positionBound := selectionEq
      rw [←same]
      exact callbackGood.2.2.2
  have initial : Good tree rowPred runtimePred frame lower upper prepared.state (prepared.state,#[],.Completed) :=
    ⟨rfl,rfl,preparedGood.every,rowsPrepared,preparedGood.wellFormed,congrArg Size.ofBytes preparedGood.capacity,
      rows_refl frame prepared.state frameRefl⟩
  have final := GeneralBorrowLoop.list_invariant _ scan
    (Good tree rowPred runtimePred frame lower upper prepared.state) step _ initial
  exact ⟨final.completed,final.runtime,final.rows,final.well,final.capacity,
    origins frame tree.locations prepared.state _ preparedOrigins.2.1 final.frames,rfl,rfl,rfl⟩

end DuplicatePrefix.GeneralBorrowConcreteRangeInvariant
