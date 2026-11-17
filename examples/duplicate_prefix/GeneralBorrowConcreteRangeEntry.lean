import duplicate_prefix.GeneralBorrowConcreteRangeInvariant

/-! Initial row authority is consumed on the saved prepared segments of the
actual resolved concrete or wildcard range loop. Only the separate output predicate must survive;
input authority is not assumed or proved preserved by a Write. -/
namespace DuplicatePrefix.GeneralBorrowConcreteRangeEntry
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess GeneralRangeMapState GeneralRangeMapOrigins
open GeneralBorrowExposedConditionalRangeFrames
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private abbrev State := DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus
private structure Good (tree : BorrowTree) (outputPred runtimePred : LocationTree → Prop)
    (frame : LocationTree → LocationTree → Prop) (lower upper : UInt64)
    (prepared : DedupRangeMap LocationTree) (state : State) : Prop where
  completed : state.2.2 = .Completed
  length : state.1.entries.size = prepared.entries.size
  runtime : Every runtimePred state.1
  rows : OwnedOn outputPred lower upper state.1
  well : state.1.WellFormed
  capacity : state.1.size = tree.locations.size
  frames : Rows frame prepared state.1

/-- Composition interface: operational wrappers derive this callback from
initial scalar authority. Saved segment data supplies its input predicate. -/
theorem access_resolved (tree : BorrowTree) (protections : ProtectedTags)
    (provenance : ProvenanceExtra) (source : Option UniIndex)
    (resolved : match provenance with
      | .concrete tag => ∃ anchor, tree.indexOfTag tag = some anchor ∧ source = some anchor
      | .wildcard => source = none) (offset len : Size)
    (kind : AccessKind) (mode : ChildrenVisitMode)
    (inputPred outputPred runtimePred : LocationTree → Prop) (frame : LocationTree → LocationTree → Prop)
    (initialOutput : ∀ location, inputPred location → outputPred location)
    (frameRefl : ∀ location, frame location location)
    (callback : ∀ location, inputPred location → runtimePred location → ∀ range,
      let accessed := source_tree_access_at tree location source kind protections mode range
      source_access_status accessed = none ∧ outputPred (source_access_location accessed) ∧
        runtimePred (source_access_location accessed) ∧ frame location (source_access_location accessed))
    (lower upper : UInt64) (owned : OwnedOn inputPred lower upper tree.locations)
    (well : tree.locations.WellFormed) (all : Every runtimePred tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : lower.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes + len.bytes).toNat ≤ upper.toNat) :
    GeneralBorrowConcreteRangeInvariant.Contract tree outputPred runtimePred frame lower upper
      (tree.performBorrowAccessRange provenance offset len kind protections mode) := by
  let prepared := tree.locations.iterMut offset len
  have preparedGood := GeneralRangeMapSafety.iter_mut
    runtimePred
    tree.locations offset len well all bounds
  have preparedOrigins := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have preparedOwners := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    inputPred lower upper owned requestLower requestUpper
  have outputOwned : OwnedOn outputPred lower upper tree.locations := by
    intro position valid positive beforeUpper afterLower
    exact initialOutput _ (owned position valid positive beforeUpper afterLower)
  have preparedOutputs := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    outputPred lower upper outputOwned requestLower requestUpper
  have rowsPrepared := preparedOutputs.2.1
  unfold BorrowTree.performBorrowAccessRange
  cases provenance
  all_goals
    first
    | (obtain ⟨anchor,mapped,chosen⟩ := resolved
       have lookup := mapped.trans chosen.symm
       have nonempty : source.isNone = false := by rw [chosen];rfl
       simp only [lookup,nonempty,Bool.false_eq_true,↓reduceIte])
    | (simp only [←resolved])
    simp only [Id.run,bind,pure,preparedGood.outcome]
    simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
      Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
    name_borrow_range_scan
    have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
        Good tree outputPred runtimePred frame lower upper prepared.state state →
        Good tree outputPred runtimePred frame lower upper prepared.state (scan cursor state).value := by
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
      have rowHere : inputPred segment.data := preparedOwners.2.2 cursor segmentBound
      have runtimeHere : runtimePred segment.data := by
        have same : segment = prepared.state.entries[position]'positionBound := selectionEq
        rw [same]
        exact preparedGood.every position positionBound
      have callbackGood := callback segment.data rowHere runtimeHere segment.range
      let accessed := source_tree_access_at tree segment.data source kind protections mode segment.range
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
    have initial : Good tree outputPred runtimePred frame lower upper prepared.state (prepared.state,#[],.Completed) :=
      ⟨rfl,rfl,preparedGood.every,rowsPrepared,preparedGood.wellFormed,congrArg Size.ofBytes preparedGood.capacity,
        rows_refl frame prepared.state frameRefl⟩
    have final := GeneralBorrowLoop.list_invariant _ scan
      (Good tree outputPred runtimePred frame lower upper prepared.state) step _ initial
    exact ⟨final.completed,final.runtime,final.rows,final.well,final.capacity,
      origins frame tree.locations prepared.state _ preparedOrigins.2.1 final.frames,rfl,rfl,rfl⟩

/-- Compatibility adapter retaining the original concrete-source API. -/
theorem access (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (anchor : UniIndex)
    (tagPresent : tree.indexOfTag tag = some anchor) (offset len : Size)
    (kind : AccessKind) (mode : ChildrenVisitMode)
    (inputPred outputPred runtimePred : LocationTree → Prop) (frame : LocationTree → LocationTree → Prop)
    (initialOutput : ∀ location, inputPred location → outputPred location)
    (frameRefl : ∀ location, frame location location)
    (callback : ∀ location, inputPred location → runtimePred location → ∀ range,
      let accessed := source_tree_access_at tree location (some anchor) kind protections mode range
      source_access_status accessed = none ∧ outputPred (source_access_location accessed) ∧
        runtimePred (source_access_location accessed) ∧ frame location (source_access_location accessed))
    (lower upper : UInt64) (owned : OwnedOn inputPred lower upper tree.locations)
    (well : tree.locations.WellFormed) (all : Every runtimePred tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : lower.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes + len.bytes).toNat ≤ upper.toNat) :
    GeneralBorrowConcreteRangeInvariant.Contract tree outputPred runtimePred frame lower upper
      (tree.performBorrowAccessRange (.concrete tag) offset len kind protections mode) := by
  exact access_resolved tree protections (.concrete tag) (some anchor) ⟨anchor,tagPresent,rfl⟩ offset len kind mode
    inputPred outputPred runtimePred frame initialOutput frameRefl callback lower upper owned well all bounds requestLower requestUpper

end DuplicatePrefix.GeneralBorrowConcreteRangeEntry

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowConcreteRangeEntry." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved entry-range dependency {dependency}"
