import duplicate_prefix.GeneralBorrowConcreteRowAccess
import duplicate_prefix.GeneralBorrowSnapshotWildcardRangeRuntime

namespace DuplicatePrefix.GeneralBorrowConcreteRowReadRange
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralRangeMapOrigins
open GeneralBorrowExposedConditionalRangeFrames
open GeneralBorrowSnapshotWildcardRangeBoth (Runtime VacantFrame authorization_locations runtime_locations)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

abbrev Row (tree : BorrowTree) (protections : ProtectedTags) (anchor selected : UniIndex)
    (maximum : Option BorTag) (location : LocationTree) : Prop :=
  Nonempty (DuplicatePrefixBorrowAuthorization.Row tree location protections (some anchor) (some selected) maximum)

theorem row_locations (tree : BorrowTree) (locations : DedupRangeMap LocationTree)
    (location : LocationTree) (protections : ProtectedTags) (anchor selected : UniIndex)
    (maximum : Option BorTag) (row : Row tree protections anchor selected maximum location) :
    Row {tree with locations := locations} protections anchor selected maximum location := by
  obtain ⟨row⟩ := row
  refine ⟨{
    wildcard := row.wildcard,rootPath := row.rootPath,rootPresent := row.rootPresent,
    cutoff := row.cutoff,normal := ?_,callbacks := ?_}⟩
  · intro source equal
    obtain ⟨normal⟩ := row.normal source equal
    exact ⟨{component := normal.component,permissions := normal.permissions}⟩
  · intro position valid different
    obtain ⟨support,read,write⟩ := row.callbacks position valid different
    exact ⟨support,authorization_locations tree locations location protections _ _ _ _ support read,
      authorization_locations tree locations location protections _ _ _ _ support write⟩

/-- Actual full concrete-source Read or Write from one raw owner row. -/
theorem location_kind (tree : BorrowTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (maximum : Option BorTag) (kind : AccessKind) (before : LocationTree)
    (row : Row tree protections anchor selected maximum before)
    (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] →
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (runtime : Runtime tree protections before) (short : tree.nodes.size < 65536)
    (mode : ChildrenVisitMode) (range : ByteRange) :
    let accessed := source_tree_access_at tree before (some anchor) kind protections mode range
    source_access_status accessed = none ∧ Row tree protections anchor selected maximum (source_access_location accessed) ∧
      Runtime tree protections (source_access_location accessed) ∧ VacantFrame tree before (source_access_location accessed) := by
  obtain ⟨row⟩ := row
  obtain ⟨complete,coherent,profile,possible,afterRow⟩ :=
    GeneralBorrowConcreteRowAccess.access_when_primary tree before protections formed anchor selected anchorNode present
      maximum kind row distinct order runtime.coherent runtime.profile runtime.possible short mode range
  refine ⟨complete,afterRow,⟨coherent,profile,possible⟩,?_⟩
  intro query missing
  rw [profile.vacant query missing,runtime.profile.vacant query missing]

/-- Physical ranged concrete access completion with the same raw owner-window rows
and runtime properties installed on the actual result tree. -/
structure Contract (before : BorrowTree) (protections : ProtectedTags)
    (anchor selected : UniIndex) (maximum : Option BorTag) (lower upper : UInt64) (result : BorrowTree.BorrowTreeAccessResult) : Prop where
  completed : result.status = .Completed
  runtime : Every (Runtime result.tree protections) result.tree.locations
  rows : OwnedOn (Row result.tree protections anchor selected maximum) lower upper result.tree.locations
  well : result.tree.locations.WellFormed
  capacity : result.tree.locations.size = before.locations.size
  frames : Origins (VacantFrame before) before.locations result.tree.locations
  nodes : result.tree.nodes = before.nodes
  roots : result.tree.roots = before.roots
  tags : result.tree.tagMapping = before.tagMapping

private abbrev State := DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus

private structure Good (tree : BorrowTree) (protections : ProtectedTags)
    (anchor selected : UniIndex) (maximum : Option BorTag) (lower upper : UInt64) (prepared : DedupRangeMap LocationTree) (state : State) : Prop where
  completed : state.2.2 = .Completed
  length : state.1.entries.size = prepared.entries.size
  runtime : Every (Runtime tree protections) state.1
  rows : OwnedOn (Row tree protections anchor selected maximum) lower upper state.1
  well : state.1.WellFormed
  capacity : state.1.size = tree.locations.size
  frames : Rows (VacantFrame tree) prepared state.1

/-- A bounded concrete Read or Write subrequest preserves the SAME raw positive owner
window rows and all physical runtime properties. The order premise is used only
when a physical primary callback can actually occur. -/
theorem access_kind (tree : BorrowTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (tag : BorTag) (anchor selected : UniIndex) (maximum : Option BorTag)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (offset len : Size) (kind : AccessKind) (mode : ChildrenVisitMode)
    (sliceStart sliceLen : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree protections (some anchor) (some selected) maximum sliceStart sliceLen)
    (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] →
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (well : tree.locations.WellFormed)
    (all : Every (Runtime tree protections) tree.locations)
    (short : tree.nodes.size < 65536)
    (requestLower : sliceStart.toNat ≤ offset.bytes.toNat)
    (requestStop : offset.bytes.toNat + len.bytes.toNat ≤ sliceStart.toNat + sliceLen.toNat) :
    Contract tree protections anchor selected maximum sliceStart (sliceStart + sliceLen)
      (tree.performBorrowAccessRange (.concrete tag) offset len kind protections mode) := by
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
  obtain ⟨anchorNode,anchorPresent⟩ := positive.sourcePresent anchor rfl
  have owned : OwnedOn (Row tree protections anchor selected maximum) sliceStart sliceStop tree.locations := positive.rows

  let prepared := tree.locations.iterMut offset len
  have preparedGood := GeneralRangeMapSafety.iter_mut
    (fun location => Runtime tree protections location)
    tree.locations offset len well all bounds
  have preparedOrigins := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have preparedOwners := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    (Row tree protections anchor selected maximum) sliceStart sliceStop owned requestLower requestUpper
  have rowsPrepared := preparedOwners.2.1
  unfold BorrowTree.performBorrowAccessRange
  simp only [tagPresent,Option.isNone_some,Bool.false_eq_true,↓reduceIte]
  simp only [Id.run,bind,pure,preparedGood.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
      Good tree protections anchor selected maximum sliceStart sliceStop prepared.state state →
      Good tree protections anchor selected maximum sliceStart sliceStop prepared.state (scan cursor state).value := by
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
    have rowHere : Row tree protections anchor selected maximum segment.data := preparedOwners.2.2 cursor segmentBound
    have runtimeHere : Runtime tree protections segment.data := by
      have same : segment = prepared.state.entries[position]'positionBound := selectionEq
      rw [same]
      exact preparedGood.every position positionBound
    have callback := location_kind tree protections formed anchor selected anchorNode anchorPresent maximum kind segment.data rowHere distinct order runtimeHere short mode segment.range
    let accessed := source_tree_access_at tree segment.data (some anchor) kind protections mode segment.range
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
      have same : segment = prepared.state.entries[position]'positionBound := selectionEq
      rw [←same]
      exact callback.2.2.2
  have initial : Good tree protections anchor selected maximum sliceStart sliceStop prepared.state (prepared.state,#[],.Completed) :=
    ⟨rfl,rfl,preparedGood.every,rowsPrepared,preparedGood.wellFormed,congrArg Size.ofBytes preparedGood.capacity,
      rows_refl (VacantFrame tree) prepared.state (by intro data query missing;rfl)⟩
  have final := GeneralBorrowLoop.list_invariant _ scan
    (Good tree protections anchor selected maximum sliceStart sliceStop prepared.state) step _ initial
  refine ⟨final.completed,?_,?_,final.well,final.capacity,
    origins (VacantFrame tree) tree.locations prepared.state _ preparedOrigins.2.1 final.frames,rfl,rfl,rfl⟩
  · intro position valid
    exact runtime_locations tree _ _ protections (final.runtime position valid)
  · intro position valid positive beforeUpper afterLower
    exact row_locations tree _ _ protections anchor selected maximum (final.rows position valid positive beforeUpper afterLower)

/-- Installing the actual ranged result reconstructs full runtime facts from
its preserved graph metadata and every physical result row. -/
theorem install (tree : BorrowTree) (global : GlobalState)
    (before : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (anchor selected : UniIndex) (maximum : Option BorTag) (lower upper : UInt64) (result : BorrowTree.BorrowTreeAccessResult)
    (contract : Contract tree global.protectedTags anchor selected maximum lower upper result) :
    DuplicatePrefixBorrowContract.RuntimeFacts result.tree global := by
  have same : result.tree = {tree with locations := result.tree.locations} := by
    have nodes := contract.nodes
    have roots := contract.roots
    have tags := contract.tags
    cases tree
    cases result with
    | mk after visited status =>
      cases after
      simp_all
  have graph := GeneralBorrowStructuralHistoryState.graph_locations tree result.tree.locations before.formed.toGraphState
  rw [←same] at graph
  refine ⟨⟨⟨graph,contract.well⟩,?_⟩,?_,?_,?_⟩
  · intro position valid
    exact (contract.runtime position valid).profile
  · intro position valid
    exact (contract.runtime position valid).coherent
  · intro position valid
    exact (contract.runtime position valid).possible
  · refine ⟨?_,before.below.protectors⟩
    rw [contract.tags]
    exact before.below.mapping

/-- The owner window retains its original length and raw positive capability
on the actual result; graph, runtime facts and vacant origins are preserved. -/
theorem access_runtime_kind (tree : BorrowTree) (global : GlobalState)
    (before : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag) (anchor selected : UniIndex) (maximum : Option BorTag)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (offset len : Size) (kind : AccessKind) (mode : ChildrenVisitMode) (sliceStart sliceLen : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags
      (some anchor) (some selected) maximum sliceStart sliceLen)
    (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] →
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (short : tree.nodes.size < 65536)
    (requestLower : sliceStart.toNat ≤ offset.bytes.toNat)
    (requestStop : offset.bytes.toNat + len.bytes.toNat ≤ sliceStart.toNat + sliceLen.toNat) :
    let result := tree.performBorrowAccessRange (.concrete tag) offset len kind global.protectedTags mode
    Contract tree global.protectedTags anchor selected maximum sliceStart (sliceStart + sliceLen) result ∧
    DuplicatePrefixBorrowContract.RuntimeFacts result.tree global ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive result.tree global.protectedTags
      (some anchor) (some selected) maximum sliceStart sliceLen) := by
  have all : Every (Runtime tree global.protectedTags) tree.locations := by
    intro position valid
    exact ⟨before.coherent position valid,before.formed.profile position valid,before.possible position valid⟩
  have contract := access_kind tree global.protectedTags before.formed.toGraphState tag anchor selected maximum tagPresent
    offset len kind mode sliceStart sliceLen positive distinct order before.formed.well all short requestLower requestStop
  refine ⟨contract,install tree global before anchor selected maximum _ _ _ contract,⟨{
    positive := positive.positive,
    bounds := ?_,sourcePresent := ?_,wildcardRoot := ?_,rows := contract.rows}⟩⟩
  · rw [contract.capacity]
    exact positive.bounds
  · intro source same
    obtain ⟨node,present⟩ := positive.sourcePresent source same
    exact ⟨node,by unfold BorrowTree.nodeAt;rw [contract.nodes];exact present⟩
  · intro impossible
    cases impossible


/-- Compatibility entry point for concrete Read rows. -/
theorem location (tree : BorrowTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (maximum : Option BorTag) (before : LocationTree)
    (row : Row tree protections anchor selected maximum before)
    (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] →
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (runtime : Runtime tree protections before) (short : tree.nodes.size < 65536)
    (mode : ChildrenVisitMode) (range : ByteRange) :
    let accessed := source_tree_access_at tree before (some anchor) .Read protections mode range
    source_access_status accessed = none ∧ Row tree protections anchor selected maximum (source_access_location accessed) ∧
      Runtime tree protections (source_access_location accessed) ∧ VacantFrame tree before (source_access_location accessed) := by
  exact location_kind tree protections formed anchor selected anchorNode present maximum .Read before row
    distinct order runtime short mode range

/-- Compatibility entry point for bounded concrete Read. -/
theorem access (tree : BorrowTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (tag : BorTag) (anchor selected : UniIndex) (maximum : Option BorTag)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (offset len : Size) (mode : ChildrenVisitMode)
    (sliceStart sliceLen : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree protections (some anchor) (some selected) maximum sliceStart sliceLen)
    (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] →
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (well : tree.locations.WellFormed)
    (all : Every (Runtime tree protections) tree.locations)
    (short : tree.nodes.size < 65536)
    (requestLower : sliceStart.toNat ≤ offset.bytes.toNat)
    (requestStop : offset.bytes.toNat + len.bytes.toNat ≤ sliceStart.toNat + sliceLen.toNat) :
    Contract tree protections anchor selected maximum sliceStart (sliceStart + sliceLen)
      (tree.performBorrowAccessRange (.concrete tag) offset len .Read protections mode) := by
  exact access_kind tree protections formed tag anchor selected maximum tagPresent offset len .Read mode
    sliceStart sliceLen positive distinct order well all short requestLower requestStop

/-- Compatibility entry point for concrete Read with runtime reconstruction. -/
theorem access_runtime (tree : BorrowTree) (global : GlobalState)
    (before : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag) (anchor selected : UniIndex) (maximum : Option BorTag)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (offset len : Size) (mode : ChildrenVisitMode) (sliceStart sliceLen : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags
      (some anchor) (some selected) maximum sliceStart sliceLen)
    (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] →
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (short : tree.nodes.size < 65536)
    (requestLower : sliceStart.toNat ≤ offset.bytes.toNat)
    (requestStop : offset.bytes.toNat + len.bytes.toNat ≤ sliceStart.toNat + sliceLen.toNat) :
    let result := tree.performBorrowAccessRange (.concrete tag) offset len .Read global.protectedTags mode
    Contract tree global.protectedTags anchor selected maximum sliceStart (sliceStart + sliceLen) result ∧
    DuplicatePrefixBorrowContract.RuntimeFacts result.tree global ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive result.tree global.protectedTags
      (some anchor) (some selected) maximum sliceStart sliceLen) := by
  exact access_runtime_kind tree global before tag anchor selected maximum tagPresent offset len .Read mode
    sliceStart sliceLen positive distinct order short requestLower requestStop

end DuplicatePrefix.GeneralBorrowConcreteRowReadRange
