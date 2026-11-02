import duplicate_prefix.GeneralBorrowExposedWildcardAccess
import duplicate_prefix.GeneralRangeMapOriginPrepare
namespace DuplicatePrefix.GeneralBorrowExposedWildcardRange
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowWildcardLeaf
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def Ready (tree : BorrowTree) (protections : ProtectedTags) (primary : UniIndex)
    (extras : List UniIndex) (nodes : UniIndex → TreeNode) (kind : AccessKind) (location : LocationTree) : Prop :=
  GeneralBorrowExposureCardinality.LocationCoherent tree location protections ∧
  location.perms.get primary = some unique ∧
  ∀ root ∈ extras, tree.nodes.get root = some (nodes root) ∧
    (nodes root).children = #[] ∧ (nodes root).isExposed = true ∧
    GeneralBorrowExposureCardinality.supports
      (GeneralBorrowExposureCardinality.effective location protections root (nodes root)) kind = true

/-- The real wildcard ranged dispatcher completes across arbitrary well-formed
partitions. Only overlapping borrowed-window rows require coherent exposure
counts and supporting roots. Bounds and initial row data derive every operation's
success; no per-row completion or poststate invariant is supplied. -/
theorem access (tree : BorrowTree) (protections : ProtectedTags)
    (primary : UniIndex) (primaryNode : TreeNode) (extras : List UniIndex) (nodes : UniIndex → TreeNode)
    (offset len : Size) (kind : AccessKind) (mode : ChildrenVisitMode)
    (roots : tree.roots = (primary::extras).toArray)
    (present : tree.nodes.get primary = some primaryNode) (leaf : primaryNode.children = #[])
    (exposed : primaryNode.isExposed = true) (short : tree.nodes.size < 65536)
    (well : tree.locations.WellFormed) (sliceStart sliceStop : UInt64)
    (owned : GeneralRangeMapOrigins.OwnedOn (Ready tree protections primary extras nodes kind) sliceStart sliceStop tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : sliceStart.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes+len.bytes).toNat ≤ sliceStop.toNat) :
    let result := tree.performBorrowAccessRange .wildcard offset len kind protections mode
    result.status = .Completed ∧ result.tree.locations.WellFormed ∧ result.tree.locations.size = tree.locations.size := by
  dsimp only
  let predicate := Ready tree protections primary extras nodes kind
  let prepared := tree.locations.iterMut offset len
  have preparedData := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have preparedGood := preparedData.1
  have preparedOwners := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    predicate sliceStart sliceStop owned requestLower requestUpper
  unfold BorrowTree.performBorrowAccessRange
  simp only
  simp only [Id.run,bind,pure,preparedGood.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  let property := fun state : DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus =>
    state.2.2 = .Completed ∧ state.1.entries.size = prepared.state.entries.size ∧
      state.1.WellFormed ∧ state.1.size = tree.locations.size
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
      property state → property (scan cursor state).value := by
    intro cursor member state good
    rcases state with ⟨current,visited,status⟩
    rcases good with ⟨statusEq,sizeEq,wellFormed,capacity⟩
    dsimp only at statusEq sizeEq
    subst status
    have cursorBound : cursor < prepared.positions.size := by
      have bounded := List.mem_range'_1.mp member
      simpa using bounded.2
    have segmentBound : cursor < prepared.segments.size := by rw [←preparedGood.lengths];exact cursorBound
    let position := prepared.positions[cursor]'cursorBound
    let segment := prepared.segments[cursor]'segmentBound
    obtain ⟨positionBound,selected⟩ := preparedGood.selected cursor cursorBound
    have localData : Ready tree protections primary extras nodes kind segment.data := preparedOwners.2.2 cursor segmentBound
    obtain ⟨after,actualLocation,accessGood,coherentAfter,cacheAfter,frameAfter⟩ := GeneralBorrowExposedWildcardAccess.access tree segment.data protections
      primary primaryNode extras nodes kind mode segment.range roots present leaf exposed localData.2.1 localData.1 short localData.2.2
    let accessed := source_tree_access_at tree segment.data none kind protections mode segment.range
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
    refine ⟨rfl,(setAtPos_length current position currentBound _).trans sizeEq,?_,?_⟩
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact replaced_wellFormed current position currentBound _ wellFormed
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact (replaced_size current position currentBound _).trans capacity
  have start : property (prepared.state,#[],.Completed) :=
    ⟨rfl,rfl,preparedGood.wellFormed,congrArg Size.ofBytes preparedGood.capacity⟩
  have final := GeneralBorrowLoop.list_invariant _ scan property step _ start
  exact ⟨final.1,final.2.2.1,final.2.2.2⟩
end DuplicatePrefix.GeneralBorrowExposedWildcardRange
