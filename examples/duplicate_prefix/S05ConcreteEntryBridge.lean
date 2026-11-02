import duplicate_prefix.GeneralBorrowCallTimeStorageBridge
import duplicate_prefix.GeneralBorrowRawFnEntry

namespace DuplicatePrefix.S05ConcreteEntryBridge
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification GeneralBorrowProjection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Positive extent and the formed partition supply a real ownership row.
Its initial ancestor path determines a selected root; no successful access or
extra root-existence premise is needed. -/
theorem selected_root (tree : BorrowTree) (protections : ProtectedTags)
    (anchor : UniIndex) (selected : Option UniIndex) (maximum : Option BorTag)
    (offset len : UInt64)
    (formed : GeneralBorrowStructuralHistorySifaState.Formed tree protections)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree protections
      (some anchor) selected maximum offset len) :
    ∃ root, selected = some root := by
  have bound := positive.bounds
  have nonempty := positive.positive
  have capacity := tree.locations.size.bytes.toNat_lt
  have sum : (offset+len).toNat = offset.toNat+len.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨position,valid,start,stop⟩ := GeneralRangeMapGeometry.covered tree.locations formed.well offset (by omega)
  obtain ⟨row⟩ := positive.rows position valid (by omega) (by omega) stop
  have path := row.rootPath anchor rfl
  cases selected with
  | some root => exact ⟨root,rfl⟩
  | none =>
    simp only [Option.map_none] at path
    have empty := List.getLast?_eq_none_iff.mp path
    have head := TraversalTree.ancestorPath_head
      (source_normal_projection tree tree.locations.entries[position].data protections).topology anchor.toNat
    rw [empty] at head
    contradiction

/-- The strengthened static runtime plus the existing positive reference and
resources construct the actual concrete borrowing-entry input. Allocation,
parent tag and byte window are retained. No Initial, access success, or
additional static condition is supplied. -/
theorem from_positive {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {before : Before} {tracker : MachineHooks.BorrowState}
    (id : AllocId) (tag : BorTag) (address len : UInt64)
    (input : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (state : DuplicatePrefixRuntimeInput.OrderedState before tracker)
    (resources : Resources options limits remaining before tracker len) :
    id = input.id ∧ ∃ raw : GeneralBorrowRawFnEntry.Input input.entry.allocation.extra input.tracker.global,
      raw.parentTag = tag ∧ raw.offset = input.offset ∧ raw.len = len ∧
      input.source = some raw.parent ∧ input.selectedRoot = some raw.selected ∧
      raw.maximum = input.maximum ∧
      DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global := by
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
  obtain ⟨same,anchor,source,tagged⟩ := binding
  have trackerSame : tracker = input.tracker := Option.some.inj (state.enabled.symm.trans input.enabled)
  subst tracker
  have member : (input.id,input.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some input.live)
  have positive := input.borrow
  rw [source] at positive
  obtain ⟨selected,selectedEq⟩ := selected_root _ _ anchor input.selectedRoot input.maximum input.offset len
    (state.formed (input.id,input.entry) member) positive
  rw [selectedEq] at positive
  obtain ⟨nodes,tags⟩ := GeneralBorrowCallTimeStorageBridge.margins input state.toState resources
  let raw : GeneralBorrowRawFnEntry.Input input.entry.allocation.extra input.tracker.global := {
    parentTag := tag, parent := anchor, selected := selected, maximum := input.maximum,
    offset := input.offset, len := len, tagged := tagged, positive := positive,
    distinct := state.roots (input.id,input.entry) member,
    order := fun _ _ => state.parent_order input.id input.entry input.live,
    short := by omega,
    nodeRoom := by omega,
    tagRoom := by
      apply UInt64.lt_iff_toNat_lt.mpr
      change input.tracker.global.nextPointerTag.value.toNat < 18446744073709551615
      omega }
  exact ⟨same,raw,rfl,rfl,rfl,source,selectedEq,rfl,
    GeneralBorrowCallTimeStorageBridge.runtime input state.toState resources⟩

/-- Concrete positive branch of the strengthened call-time Contract, connected
to the existing borrowing-entry API. The physical caller/return-slot bridge
and whole-call Target are separate obligations. -/
theorem from_contract {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len : UInt64)
    (contract : Contract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) :
    ∃ input : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len,
      id = input.id ∧ ∃ raw : GeneralBorrowRawFnEntry.Input input.entry.allocation.extra input.tracker.global,
        raw.parentTag = tag ∧ raw.offset = input.offset ∧ raw.len = len ∧
        input.source = some raw.parent ∧ input.selectedRoot = some raw.selected ∧
        raw.maximum = input.maximum ∧
        DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global := by
  cases contract.reference with
  | empty zero metadata => exact False.elim (nonempty zero)
  | positive pointer encoding input =>
    have same := DuplicatePrefixSliceArgument.Argument.pointer.inj encoding
    subst pointer
    exact ⟨input,from_positive id tag address len input contract.runtime contract.resources⟩

end
end DuplicatePrefix.S05ConcreteEntryBridge
