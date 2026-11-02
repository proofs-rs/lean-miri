import duplicate_prefix.GeneralBorrowExposedConditionalRangeFrames
import duplicate_prefix.GeneralBorrowProtectedReadRangeExposureCache
namespace DuplicatePrefix.GeneralBorrowExposedConditionalRangeAccess
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralRangeMapOrigins
open GeneralBorrowExposedConditionalRangeData GeneralBorrowExposedConditionalRangeFrames
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Physical ranged wildcard completion and reusable output invariants. Frames
refer to actual original values at each byte, so preparation splits/merges do
not replace the original per-row cache provenance with an index assumption. -/
structure Contract (before : BorrowTree) (protections : ProtectedTags) (kind : AccessKind)
    (lower upper : UInt64) (result : BorrowTree.BorrowTreeAccessResult) : Prop where
  completed : result.status = .Completed
  coherent : Every (fun location => GeneralBorrowExposureCardinality.LocationCoherent result.tree location protections) result.tree.locations
  profile : OwnedOn (Profile result.tree protections kind) lower upper result.tree.locations
  well : result.tree.locations.WellFormed
  capacity : result.tree.locations.size = before.locations.size
  frames : Origins (Frame kind) before.locations result.tree.locations
  nodes : result.tree.nodes = before.nodes
  roots : result.tree.roots = before.roots
  tags : result.tree.tagMapping = before.tagMapping

private abbrev State := DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus

private structure Good (tree : BorrowTree) (protections : ProtectedTags) (kind : AccessKind)
    (lower upper : UInt64) (prepared : DedupRangeMap LocationTree) (state : State) : Prop where
  completed : state.2.2 = .Completed
  length : state.1.entries.size = prepared.entries.size
  coherent : Every (fun location => GeneralBorrowExposureCardinality.LocationCoherent tree location protections) state.1
  profile : OwnedOn (Profile tree protections kind) lower upper state.1
  well : state.1.WellFormed
  capacity : state.1.size = tree.locations.size
  frames : Rows (Frame kind) prepared state.1

/-- Actual `performBorrowAccessRange .wildcard` on arbitrary well-formed byte
partitions and requested subslices. Only intersecting owner-window rows need
the raw conditional permission/Covers/primary-exposure contracts. Global cache
coherence is retained, including disjoint rows; no callback success is assumed.
The Nat bounds are explicit and derive non-wrapping source range preparation.
SIFA scheduling is derived inside the frozen actual location visitor proofs. -/
theorem access (tree : BorrowTree) (protections : ProtectedTags) (primary : UniIndex) (extras : List UniIndex)
    (offset len : Size) (kind : AccessKind) (mode : ChildrenVisitMode)
    (roots : tree.roots = (primary::extras).toArray) (well : tree.locations.WellFormed)
    (all : Every (fun location => GeneralBorrowExposureCardinality.LocationCoherent tree location protections) tree.locations)
    (sliceStart sliceStop : UInt64)
    (owned : OwnedOn (Ready tree protections primary extras kind) sliceStart sliceStop tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : sliceStart.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes+len.bytes).toNat ≤ sliceStop.toNat) :
    Contract tree protections kind sliceStart sliceStop
      (tree.performBorrowAccessRange .wildcard offset len kind protections mode) := by
  let prepared := tree.locations.iterMut offset len
  have preparedGood := GeneralRangeMapSafety.iter_mut
    (fun location => GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    tree.locations offset len well all bounds
  have preparedOrigins := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have preparedOwners := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    (Ready tree protections primary extras kind) sliceStart sliceStop owned requestLower requestUpper
  have profileBefore : OwnedOn (Profile tree protections kind) sliceStart sliceStop tree.locations := by
    intro position valid positive start stop
    exact ready_profile tree protections primary extras kind _ (owned position valid positive start stop)
  have profilePrepared := refines_owned_on tree.locations prepared.state (Profile tree protections kind)
    sliceStart sliceStop preparedGood.wellFormed preparedOrigins.2.1 profileBefore
  unfold BorrowTree.performBorrowAccessRange
  simp only
  simp only [Id.run,bind,pure,preparedGood.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
      Good tree protections kind sliceStart sliceStop prepared.state state →
      Good tree protections kind sliceStart sliceStop prepared.state (scan cursor state).value := by
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
    obtain ⟨positionBound,selected⟩ := preparedGood.selected cursor cursorBound
    have readyHere : Ready tree protections primary extras kind segment.data := preparedOwners.2.2 cursor segmentBound
    have callback := GeneralBorrowExposedConditionalRangeData.location tree protections primary extras kind mode segment.range segment.data roots readyHere
    let accessed := source_tree_access_at tree segment.data none kind protections mode segment.range
    let mutation := current.setAtPos position (source_access_location accessed)
    have currentBound : position < current.entries.size := by rw [good.length];exact positionBound
    have positionLookup : (tree.locations.iterMut offset len).positions[cursor]? = some position := Array.getElem?_eq_getElem cursorBound
    have segmentLookup : (tree.locations.iterMut offset len).segments[cursor]? = some segment := Array.getElem?_eq_getElem segmentBound
    have actual : scan cursor (current,visited,.Completed) =
        .yield (mutation.state,visited.push ⟨segment.range,source_access_normal accessed⟩,.Completed) := by
      simp only [scan,beq_self_eq_true,↓reduceIte,positionLookup,segmentLookup,
        setAtPos_success current position currentBound,callback.1]
      rfl
    rw [actual]
    refine ⟨rfl,(setAtPos_length current position currentBound _).trans good.length,?_,?_,?_,?_,?_⟩
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact replaced_every _ current position currentBound _ good.coherent callback.2.2.1
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact replaced_owned_on _ sliceStart sliceStop current position currentBound _ good.profile callback.2.1
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact replaced_wellFormed current position currentBound _ good.well
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact (replaced_size current position currentBound _).trans good.capacity
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      apply replaced_rows (Frame kind) prepared.state current position currentBound _ good.frames positionBound
      have same : segment = prepared.state.entries[position]'positionBound := selected
      rw [←same]
      exact callback.2.2.2
  have initial : Good tree protections kind sliceStart sliceStop prepared.state (prepared.state,#[],.Completed) :=
    ⟨rfl,rfl,preparedGood.every,profilePrepared,preparedGood.wellFormed,congrArg Size.ofBytes preparedGood.capacity,
      rows_refl (Frame kind) prepared.state (frame_refl kind)⟩
  have final := GeneralBorrowLoop.list_invariant _ scan
    (Good tree protections kind sliceStart sliceStop prepared.state) step _ initial
  exact ⟨final.completed,final.coherent,final.profile,final.well,final.capacity,
    origins (Frame kind) tree.locations prepared.state _ preparedOrigins.2.1 final.frames,rfl,rfl,rfl⟩
end DuplicatePrefix.GeneralBorrowExposedConditionalRangeAccess
