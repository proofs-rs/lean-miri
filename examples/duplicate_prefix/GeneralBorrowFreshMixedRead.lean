import duplicate_prefix.GeneralBorrowFreshMixedConstructor
namespace DuplicatePrefix.GeneralBorrowFreshMixedRead
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralRangeMapOrigins
open DuplicatePrefix.GeneralBorrowFreshReleaseMixed
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
private theorem replaced_owned_on (predicate : α → Prop) (lower upper : UInt64)
    (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size) (data : α)
    (owned : OwnedOn predicate lower upper map) (newOwned : predicate data) :
    OwnedOn predicate lower upper (replaced map position valid data) := by
  intro index bounded positive beforeUpper afterLower
  have oldBound : index < map.entries.size := by simpa only [replaced_length] using bounded
  rw [replaced_range map position valid data index oldBound] at beforeUpper afterLower
  by_cases same : position = index
  · subst index
    simpa [replaced] using newOwned
  · have previous := owned index oldBound positive beforeUpper afterLower
    simpa [replaced,Array.getElem_set,same] using previous

/-- Real single-root ranged access needs ownership only where the caller's
borrowed slice overlaps the range partition. Ownership at disjoint locations
is not required. The data ownership strength is retained, including write ownership
through a read, while map well-formedness and capacity are preserved. -/
theorem access (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (anchor root : UniIndex)
    (offset len : Size) (writable : Nat → Bool) (mode : ChildrenVisitMode)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (well : tree.locations.WellFormed) (sliceStart sliceStop : UInt64)
    (owned : OwnedOn (Combined tree protections anchor writable) sliceStart sliceStop tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : sliceStart.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes+len.bytes).toNat ≤ sliceStop.toNat) :
    let result := tree.performNormalAccessRange tag offset len .Read protections mode
    result.status = .Completed ∧
      OwnedOn (Combined result.tree protections anchor writable) sliceStart sliceStop result.tree.locations ∧
      result.tree.locations.WellFormed ∧ result.tree.locations.size = tree.locations.size := by
  dsimp only
  let predicate := Combined tree protections anchor writable
  let prepared := tree.locations.iterMut offset len
  have preparedData := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have preparedGood := preparedData.1
  have preparedOwners := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    predicate sliceStart sliceStop owned requestLower requestUpper
  unfold BorrowTree.performNormalAccessRange BorrowTree.performBorrowAccessRange
  simp only [tagPresent,Option.isNone_some,Bool.false_eq_true,↓reduceIte]
  simp only [Id.run,bind,pure,preparedGood.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  let property := fun state : DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus =>
    state.2.2 = .Completed ∧ state.1.entries.size = prepared.state.entries.size ∧
      OwnedOn predicate sliceStart sliceStop state.1 ∧ state.1.WellFormed ∧ state.1.size = tree.locations.size
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
      property state → property (scan cursor state).value := by
    intro cursor member state good
    rcases state with ⟨current,visited,status⟩
    rcases good with ⟨statusEq,sizeEq,localOwned,wellFormed,capacity⟩
    dsimp only at statusEq sizeEq
    subst status
    have cursorBound : cursor < prepared.positions.size := by
      have bounded := List.mem_range'_1.mp member
      simpa using bounded.2
    have segmentBound : cursor < prepared.segments.size := by rw [←preparedGood.lengths];exact cursorBound
    let position := prepared.positions[cursor]'cursorBound
    let segment := prepared.segments[cursor]'segmentBound
    obtain ⟨positionBound,selected⟩ := preparedGood.selected cursor cursorBound
    have ownedHere : predicate segment.data := preparedOwners.2.2 cursor segmentBound
    have updatedOwned := GeneralBorrowRangePreserves.location_owned tree segment.data protections anchor root .Read .Read mode segment.range (fun _ => rfl) fits
      ownedHere.1 depth children anchorNode anchorPresent roots covered
    have updatedMixed := GeneralBorrowFreshReleaseMixed.mixed_location tree segment.data protections anchor root mode segment.range writable fits
      ownedHere.1 ownedHere.2 depth children anchorNode anchorPresent roots covered
    obtain ⟨⟨forest⟩,owner⟩ := ownedHere.1
    have accessGood := GeneralBorrowSingleRoot.access_at tree segment.data protections anchor root .Read mode segment.range
      forest (GeneralBorrowRangePreserves.owned_for_access _ anchor.toNat .Read .Read (fun _ => rfl) owner)
      depth children anchorNode anchorPresent roots covered
    let access := source_tree_access_at tree segment.data (some anchor) .Read protections mode segment.range
    let mutation := current.setAtPos position (source_access_location access)
    have currentBound : position < current.entries.size := by rw [sizeEq];exact positionBound
    have positionLookup : (tree.locations.iterMut offset len).positions[cursor]? = some position := Array.getElem?_eq_getElem cursorBound
    have segmentLookup : (tree.locations.iterMut offset len).segments[cursor]? = some segment := Array.getElem?_eq_getElem segmentBound
    have actual : scan cursor (current,visited,.Completed) =
        .yield (mutation.state,visited.push ⟨segment.range,source_access_normal access⟩,.Completed) := by
      simp only [scan,beq_self_eq_true,↓reduceIte,positionLookup,segmentLookup,
        setAtPos_success current position currentBound,accessGood]
      rfl
    rw [actual]
    refine ⟨rfl,(setAtPos_length current position currentBound _).trans sizeEq,?_,?_,?_⟩
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact replaced_owned_on predicate sliceStart sliceStop current position currentBound _ localOwned ⟨updatedOwned,updatedMixed⟩
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact replaced_wellFormed current position currentBound _ wellFormed
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact (replaced_size current position currentBound _).trans capacity
  have initial : property (prepared.state,#[],.Completed) :=
    ⟨rfl,rfl,preparedOwners.2.1,preparedGood.wellFormed,congrArg Size.ofBytes preparedGood.capacity⟩
  have final := GeneralBorrowLoop.list_invariant _ scan property step _ initial
  exact ⟨final.1,final.2.2.1,final.2.2.2.1,final.2.2.2.2⟩

end DuplicatePrefix.GeneralBorrowFreshMixedRead
#print axioms DuplicatePrefix.GeneralBorrowFreshMixedRead.access
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshMixedRead." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved ranged mixed Read preservation dependency {dependency}"
