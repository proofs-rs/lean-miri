import duplicate_prefix.GeneralBorrowSnapshotWildcardRowReadBoth
import duplicate_prefix.GeneralBorrowSnapshotWildcardRowWriteBoth
import duplicate_prefix.GeneralBorrowExposedConditionalRangeAccess

namespace DuplicatePrefix.GeneralBorrowSnapshotWildcardRangeBoth
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralRangeMapOrigins
open GeneralBorrowExposedConditionalRangeFrames
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

abbrev Row (tree : BorrowTree) (protections : ProtectedTags) (location : LocationTree) : Prop :=
  Nonempty (DuplicatePrefixBorrowAuthorization.Row tree location protections none none none)

structure Runtime (tree : BorrowTree) (protections : ProtectedTags) (location : LocationTree) : Prop where
  coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections
  profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections
  possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location

def VacantFrame (tree : BorrowTree) (before after : LocationTree) : Prop :=
  ∀ query, tree.nodes.get query = none → after.perms.get query = before.perms.get query

theorem authorization_locations (tree : BorrowTree) (locations : DedupRangeMap LocationTree)
    (location : LocationTree) (protections : ProtectedTags) (root : UniIndex) (position : Nat)
    (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (authorization : DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections root position maximum kind support) :
    DuplicatePrefixResidualSupportAuthorization.Authorization {tree with locations := locations}
      location protections root position maximum kind support := by
  refine ⟨authorization.rooted,authorization.present,authorization.children,authorization.covers,
    authorization.possible,?_,authorization.witness⟩
  intro before after legalBefore legalAfter subset index node inside present retained
  exact authorization.queries before after ⟨legalBefore.distinct,legalBefore.allowed⟩
    ⟨legalAfter.distinct,legalAfter.allowed⟩ subset index node inside present retained

theorem row_locations (tree : BorrowTree) (locations : DedupRangeMap LocationTree)
    (location : LocationTree) (protections : ProtectedTags) (row : Row tree protections location) :
    Row {tree with locations := locations} protections location := by
  obtain ⟨row⟩ := row
  refine ⟨{wildcard := fun _ => rfl,rootPath := ?_,rootPresent := ?_,cutoff := rfl,normal := ?_,callbacks := ?_}⟩
  · intro anchor impossible;cases impossible
  · intro root impossible;cases impossible
  · intro anchor impossible;cases impossible
  · intro position valid different
    obtain ⟨support,read,write⟩ := row.callbacks position valid different
    exact ⟨support,authorization_locations tree locations location protections _ _ _ _ support read,
      authorization_locations tree locations location protections _ _ _ _ support write⟩

theorem runtime_locations (tree : BorrowTree) (locations : DedupRangeMap LocationTree)
    (location : LocationTree) (protections : ProtectedTags) (runtime : Runtime tree protections location) :
    Runtime {tree with locations := locations} protections location :=
  ⟨runtime.coherent,⟨runtime.profile.present,runtime.profile.vacant⟩,runtime.possible⟩

/-- Both actual full-row operations expose one common raw-data interface.
This dispatcher imposes no old Ready, scalar profile or successful-access input. -/
theorem location (tree : BorrowTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (before : LocationTree) (row : Row tree protections before)
    (distinct : tree.roots.toList.Nodup) (nonempty : 0 < tree.roots.size)
    (runtime : Runtime tree protections before) (short : tree.nodes.size < 65536)
    (kind : AccessKind) (mode : ChildrenVisitMode) (range : ByteRange) :
    let accessed := source_tree_access_at tree before none kind protections mode range
    source_access_status accessed = none ∧ Row tree protections (source_access_location accessed) ∧
      Runtime tree protections (source_access_location accessed) ∧ VacantFrame tree before (source_access_location accessed) := by
  obtain ⟨row⟩ := row
  cases kind with
  | Read =>
    obtain ⟨complete,coherent,profile,possible,_,_,_,vacant,afterRow⟩ :=
      GeneralBorrowSnapshotWildcardRowReadBoth.access tree before protections formed row distinct nonempty
        runtime.coherent runtime.profile runtime.possible short mode range
    exact ⟨complete,afterRow,⟨coherent,profile,possible⟩,vacant⟩
  | Write =>
    obtain ⟨complete,coherent,profile,possible,vacant,afterRow⟩ :=
      GeneralBorrowSnapshotWildcardRowWriteBoth.access tree before protections formed row distinct nonempty
        runtime.coherent runtime.profile runtime.possible short mode range
    exact ⟨complete,afterRow,⟨coherent,profile,possible⟩,vacant⟩

/-- Physical ranged wildcard completion with the same raw owner-window rows
and runtime properties installed on the actual result tree. -/
structure Contract (before : BorrowTree) (protections : ProtectedTags)
    (lower upper : UInt64) (result : BorrowTree.BorrowTreeAccessResult) : Prop where
  completed : result.status = .Completed
  runtime : Every (Runtime result.tree protections) result.tree.locations
  rows : OwnedOn (Row result.tree protections) lower upper result.tree.locations
  well : result.tree.locations.WellFormed
  capacity : result.tree.locations.size = before.locations.size
  frames : Origins (VacantFrame before) before.locations result.tree.locations
  nodes : result.tree.nodes = before.nodes
  roots : result.tree.roots = before.roots
  tags : result.tree.tagMapping = before.tagMapping

private abbrev State := DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus

private structure Good (tree : BorrowTree) (protections : ProtectedTags)
    (lower upper : UInt64) (prepared : DedupRangeMap LocationTree) (state : State) : Prop where
  completed : state.2.2 = .Completed
  length : state.1.entries.size = prepared.entries.size
  runtime : Every (Runtime tree protections) state.1
  rows : OwnedOn (Row tree protections) lower upper state.1
  well : state.1.WellFormed
  capacity : state.1.size = tree.locations.size
  frames : Rows (VacantFrame tree) prepared state.1

/-- The actual wildcard range operation on any bounded subrequest of a raw
S01 positive wildcard window. The source iterator derives preparation, selected
rows and every callback result; no Ready, global permission profile, leaf,
noFree or successful-operation premise is accepted. Both permission candidates
are retained on the SAME owner window for either kind and either visit mode. -/
theorem access (tree : BorrowTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (offset len : Size) (kind : AccessKind) (mode : ChildrenVisitMode)
    (sliceStart sliceLen : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree protections none none none sliceStart sliceLen)
    (distinct : tree.roots.toList.Nodup) (well : tree.locations.WellFormed)
    (all : Every (Runtime tree protections) tree.locations)
    (short : tree.nodes.size < 65536)
    (requestLower : sliceStart.toNat ≤ offset.bytes.toNat)
    (requestStop : offset.bytes.toNat + len.bytes.toNat ≤ sliceStart.toNat + sliceLen.toNat) :
    Contract tree protections sliceStart (sliceStart + sliceLen)
      (tree.performBorrowAccessRange .wildcard offset len kind protections mode) := by
  let sliceStop := sliceStart + sliceLen
  have bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat := by
    have ownerBounds := positive.bounds
    omega
  have fits : offset.bytes.toNat + len.bytes.toNat < 2^64 :=
    Nat.lt_of_le_of_lt bounds tree.locations.size.bytes.toNat_lt
  have ownerFits : sliceStart.toNat + sliceLen.toNat < 2^64 :=
    Nat.lt_of_le_of_lt positive.bounds tree.locations.size.bytes.toNat_lt
  have requestUpper : (offset.bytes + len.bytes).toNat ≤ sliceStop.toNat := by
    dsimp only [sliceStop]
    rw [UInt64.toNat_add,UInt64.toNat_add,Nat.mod_eq_of_lt fits,Nat.mod_eq_of_lt ownerFits]
    exact requestStop
  have nonempty : 0 < tree.roots.size := positive.wildcardRoot rfl
  have owned : OwnedOn (Row tree protections) sliceStart sliceStop tree.locations := positive.rows

  let prepared := tree.locations.iterMut offset len
  have preparedGood := GeneralRangeMapSafety.iter_mut
    (fun location => Runtime tree protections location)
    tree.locations offset len well all bounds
  have preparedOrigins := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have preparedOwners := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    (Row tree protections) sliceStart sliceStop owned requestLower requestUpper
  have rowsPrepared := preparedOwners.2.1
  unfold BorrowTree.performBorrowAccessRange
  simp only
  simp only [Id.run,bind,pure,preparedGood.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
      Good tree protections sliceStart sliceStop prepared.state state →
      Good tree protections sliceStart sliceStop prepared.state (scan cursor state).value := by
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
    have rowHere : Row tree protections segment.data := preparedOwners.2.2 cursor segmentBound
    have runtimeHere : Runtime tree protections segment.data := by
      have same : segment = prepared.state.entries[position]'positionBound := selected
      rw [same]
      exact preparedGood.every position positionBound
    have callback := location tree protections formed segment.data rowHere distinct nonempty runtimeHere short kind mode segment.range
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
      exact replaced_every _ current position currentBound _ good.runtime callback.2.2.1
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact replaced_owned_on _ sliceStart sliceStop current position currentBound _ good.rows callback.2.1
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact replaced_wellFormed current position currentBound _ good.well
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact (replaced_size current position currentBound _).trans good.capacity
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      apply replaced_rows (VacantFrame tree) prepared.state current position currentBound _ good.frames positionBound
      have same : segment = prepared.state.entries[position]'positionBound := selected
      rw [←same]
      exact callback.2.2.2
  have initial : Good tree protections sliceStart sliceStop prepared.state (prepared.state,#[],.Completed) :=
    ⟨rfl,rfl,preparedGood.every,rowsPrepared,preparedGood.wellFormed,congrArg Size.ofBytes preparedGood.capacity,
      rows_refl (VacantFrame tree) prepared.state (by intro data query missing;rfl)⟩
  have final := GeneralBorrowLoop.list_invariant _ scan
    (Good tree protections sliceStart sliceStop prepared.state) step _ initial
  refine ⟨final.completed,?_,?_,final.well,final.capacity,
    origins (VacantFrame tree) tree.locations prepared.state _ preparedOrigins.2.1 final.frames,rfl,rfl,rfl⟩
  · intro position valid
    exact runtime_locations tree _ _ protections (final.runtime position valid)
  · intro position valid positive beforeUpper afterLower
    exact row_locations tree _ _ protections (final.rows position valid positive beforeUpper afterLower)

end DuplicatePrefix.GeneralBorrowSnapshotWildcardRangeBoth
