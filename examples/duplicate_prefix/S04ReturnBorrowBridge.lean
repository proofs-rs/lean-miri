import duplicate_prefix.S05ConcreteEntryBridge
import duplicate_prefix.S05WildcardEntryBridge
import duplicate_prefix.GeneralBorrowConcreteRowReadRange
import duplicate_prefix.GeneralBorrowSnapshotWildcardRangeRuntime

namespace DuplicatePrefix.S04ReturnBorrowBridge
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- The extra provenance selected by the production pointer resolver: concrete
allocation identity is carried separately and only the concrete tag enters the
borrow-tree access. Wildcard remains wildcard. -/
def extra : Provenance → ProvenanceExtra
  | .concrete _ tag => .concrete tag
  | .wildcard => .wildcard

/-- Raw return-place data and the existing runtime/resources supply its SAME
live allocation's runtime, distinct roots and access-counter headroom. The byte
need not be initialized; no contents or initialization-success field is used. -/
theorem runtime {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {before : Before} {tracker : MachineHooks.BorrowState}
    {place : MPlaceTy Provenance} {len : UInt64}
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (resources : Resources options limits remaining before tracker len) :
    DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global ∧
      input.entry.allocation.extra.roots.toList.Nodup ∧
      input.entry.allocation.extra.nodes.size < 65536 := by
  have same : tracker = input.tracker := Option.some.inj (state.enabled.symm.trans input.enabled)
  subst tracker
  have member : (input.id,input.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some input.live)
  have room := resources.nodeRoom (input.id,input.entry) member
  dsimp only at room
  exact ⟨{
    formed := state.formed (input.id,input.entry) member
    coherent := state.coherent (input.id,input.entry) member
    possible := state.possible (input.id,input.entry) member
    below := resources.tagsBelow (input.id,input.entry) member },
    state.roots (input.id,input.entry) member,by omega⟩

/-- The initial writable bool capability derives the actual one-byte Write
borrow access, retaining the original capability and installed runtime. Both
concrete and wildcard provenance are covered, with arbitrary child visit mode.
This does not yet transport the destination through input retags/copy/release
or execute the physical byte store; it is the initial-state access leaf. -/
theorem write {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {before : Before} {tracker : MachineHooks.BorrowState}
    {place : MPlaceTy Provenance} {len : UInt64}
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (state : DuplicatePrefixRuntimeInput.OrderedState before tracker)
    (resources : Resources options limits remaining before tracker len)
    (mode : ChildrenVisitMode) :
    let result := input.entry.allocation.extra.performBorrowAccessRange (extra input.pointer.provenance)
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write input.tracker.global.protectedTags mode
    result.status = .Completed ∧
      DuplicatePrefixBorrowContract.RuntimeFacts result.tree input.tracker.global ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive result.tree input.tracker.global.protectedTags
        input.source input.selectedRoot input.maximum input.offset 1) ∧
      result.tree.locations.size = input.entry.allocation.extra.locations.size ∧
      result.tree.nodes = input.entry.allocation.extra.nodes ∧
      result.tree.roots = input.entry.allocation.extra.roots ∧
      result.tree.tagMapping = input.entry.allocation.extra.tagMapping := by
  obtain ⟨beforeRuntime,distinct,short⟩ := runtime input state.toState resources
  cases provenance : input.pointer.provenance with
  | concrete id tag =>
    have binding := input.binding
    simp only [DuplicatePrefixReferenceInput.Binding,provenance] at binding
    obtain ⟨same,anchor,source,tagged⟩ := binding
    have positive := input.borrow
    rw [source] at positive
    obtain ⟨selected,selectedEq⟩ := S05ConcreteEntryBridge.selected_root _ _ anchor input.selectedRoot
      input.maximum input.offset 1 beforeRuntime.formed positive
    rw [selectedEq] at positive
    obtain ⟨contract,afterRuntime,afterPositive⟩ := GeneralBorrowConcreteRowReadRange.access_runtime_kind
      input.entry.allocation.extra input.tracker.global beforeRuntime tag anchor selected input.maximum tagged
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write mode input.offset 1 positive distinct
      (fun _ _ => state.parent_order input.id input.entry input.live) short (Nat.le_refl _) (Nat.le_refl _)
    simp only [extra]
    refine ⟨contract.completed,afterRuntime,?_,contract.capacity,contract.nodes,contract.roots,contract.tags⟩
    rw [source,selectedEq]
    exact afterPositive
  | wildcard =>
    have binding := input.binding
    simp only [DuplicatePrefixReferenceInput.Binding,provenance] at binding
    obtain ⟨source,nonstrict,exposed,geometry⟩ := binding
    have positive := input.borrow
    rw [source] at positive
    obtain ⟨selected,maximum⟩ := S05WildcardEntryBridge.wildcard_metadata _ _ input.selectedRoot
      input.maximum input.offset 1 beforeRuntime.formed positive
    rw [selected,maximum] at positive
    obtain ⟨contract,afterRuntime⟩ := GeneralBorrowSnapshotWildcardRangeRuntime.access
      input.entry.allocation.extra input.tracker.global beforeRuntime (Size.ofBytes input.offset)
      (Size.ofBytes 1) .Write mode input.offset 1 positive distinct short (Nat.le_refl _) (Nat.le_refl _)
    have afterPositive : Nonempty (DuplicatePrefixBorrowAuthorization.Positive
        (input.entry.allocation.extra.performBorrowAccessRange .wildcard (Size.ofBytes input.offset)
          (Size.ofBytes 1) .Write input.tracker.global.protectedTags mode).tree input.tracker.global.protectedTags
        none none none input.offset 1) := by
      refine ⟨{positive := positive.positive,bounds := ?_,sourcePresent := ?_,wildcardRoot := ?_,rows := contract.rows}⟩
      · rw [contract.capacity]
        exact positive.bounds
      · intro anchor impossible;cases impossible
      · intro unused
        rw [contract.roots]
        exact positive.wildcardRoot rfl
    simp only [extra]
    refine ⟨contract.completed,afterRuntime,?_,contract.capacity,contract.nodes,contract.roots,contract.tags⟩
    rw [source,selected,maximum]
    exact afterPositive

end
end DuplicatePrefix.S04ReturnBorrowBridge
