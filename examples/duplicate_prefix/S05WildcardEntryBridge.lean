import duplicate_prefix.GeneralBorrowCallTimeStorageBridge
import duplicate_prefix.GeneralBorrowRawWildcardFnEntryResources

namespace DuplicatePrefix.S05WildcardEntryBridge
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- One actual overlapping partition row fixes the wildcard's shared root and
cutoff metadata. No callback, lookup or operation outcome is assumed. -/
theorem wildcard_metadata (tree : BorrowTree) (protections : ProtectedTags)
    (selected : Option UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (formed : GeneralBorrowStructuralHistorySifaState.Formed tree protections)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree protections none selected maximum offset len) :
    selected = none ∧ maximum = none := by
  have bound := positive.bounds
  have nonempty := positive.positive
  have capacity := tree.locations.size.bytes.toNat_lt
  have sum : (offset+len).toNat = offset.toNat+len.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨position,valid,start,stop⟩ := GeneralRangeMapGeometry.covered tree.locations formed.well offset (by omega)
  obtain ⟨row⟩ := positive.rows position valid (by omega) (by omega) stop
  exact ⟨row.wildcard rfl,row.wildcard_cutoff⟩

/-- Existing reference, runtime and resource candidates supply all initial
premises of the actual wildcard borrowing entry. The original State suffices:
no parent-tag order or stronger ownership/profile condition is added. -/
theorem from_positive {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {before : Before} {tracker : MachineHooks.BorrowState}
    (address len : UInt64)
    (input : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (resources : Resources options limits remaining before tracker len) :
    input.source = none ∧ input.selectedRoot = none ∧ input.maximum = none ∧
      DuplicatePrefixBorrowAuthorization.Positive input.entry.allocation.extra input.tracker.global.protectedTags
        none none none input.offset len ∧
      DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global ∧
      input.entry.allocation.extra.roots.toList.Nodup ∧
      input.entry.allocation.extra.nodes.size < 65536 ∧
      input.entry.allocation.extra.nodes.size+1 ≤ 4294967295 ∧
      input.tracker.global.nextPointerTag.value < 18446744073709551615 := by
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
  obtain ⟨source,mode,exposed,geometry⟩ := binding
  have trackerSame : tracker = input.tracker := Option.some.inj (state.enabled.symm.trans input.enabled)
  subst tracker
  have member : (input.id,input.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some input.live)
  have positive := input.borrow
  rw [source] at positive
  obtain ⟨selected,maximum⟩ := wildcard_metadata _ _ input.selectedRoot input.maximum input.offset len
    (state.formed (input.id,input.entry) member) positive
  rw [selected,maximum] at positive
  obtain ⟨nodes,tags⟩ := GeneralBorrowCallTimeStorageBridge.margins input state resources
  refine ⟨source,selected,maximum,positive,
    GeneralBorrowCallTimeStorageBridge.runtime input state resources,
    state.roots (input.id,input.entry) member,by omega,by omega,?_⟩
  apply UInt64.lt_iff_toNat_lt.mpr
  change input.tracker.global.nextPointerTag.value.toNat < 18446744073709551615
  omega

/-- From the same initial allocation and byte window, execute real fresh-tag
allocation, protector registration, wildcard Read and protected root insertion.
The resulting child has the full Read/Write capability and bounded Write
activity. This is a borrowing component, not a typed MIR whole-call theorem. -/
theorem invoke_positive {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {before : Before} {tracker : MachineHooks.BorrowState}
    (address len : UInt64)
    (input : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (resources : Resources options limits remaining before tracker len)
    (frame : FrameState) :
    ∃ output, GeneralBorrowRawWildcardFnEntryRuntime.operation input.entry.allocation.extra
        input.tracker.global frame input.id input.offset len = .ok output ∧
      output.tag = input.tracker.global.nextPointerTag ∧
      output.frame.protectedTags = frame.protectedTags.push (input.id,output.tag) ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      output.child.tree.locations.size = input.entry.allocation.extra.locations.size ∧
      output.child.tree.nodes.size ≤ input.entry.allocation.extra.nodes.size+1 ∧
      ∃ child,output.child.tree.indexOfTag output.tag = some child ∧
        output.child.tree.roots = input.entry.allocation.extra.roots.push child ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive output.child.tree output.global.protectedTags
          (some child) (some child) (some output.tag) input.offset len) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write input.offset (input.offset+len) := by
  obtain ⟨source,selected,maximum,positive,runtime,distinct,short,nodes,tags⟩ :=
    from_positive address len input state resources
  obtain ⟨output,actual,tag,registered,held,completed,constructed,afterRuntime,capacity,growth,
    child,present,roots,capability,activity,geometry⟩ :=
    GeneralBorrowRawWildcardFnEntryResources.invoke input.entry.allocation.extra input.tracker.global
      frame input.id runtime input.offset len positive distinct short nodes tags
  exact ⟨output,actual,tag,held,completed,constructed,afterRuntime,capacity,growth,
    child,present,roots,capability,activity⟩

/-- The positive wildcard branch of the original broader Contract already
supplies the real entry. Stronger Contract callers can use Contract.toLegacy.
No operation success, future state, Initial, or extra static restriction is an
input, and the same supplied id/offset/length are used by the derived operation. -/
theorem from_contract {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} (address len : UInt64)
    (contract : LegacyContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (frame : FrameState) :
    ∃ input : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new .wildcard (Size.ofBytes address)) len,
      ∃ output, GeneralBorrowRawWildcardFnEntryRuntime.operation input.entry.allocation.extra
          input.tracker.global frame input.id input.offset len = .ok output ∧
        output.tag = input.tracker.global.nextPointerTag ∧
        output.frame.protectedTags = frame.protectedTags.push (input.id,output.tag) ∧
        output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
        DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
        output.child.tree.locations.size = input.entry.allocation.extra.locations.size ∧
        output.child.tree.nodes.size ≤ input.entry.allocation.extra.nodes.size+1 ∧
        ∃ child,output.child.tree.indexOfTag output.tag = some child ∧
          output.child.tree.roots = input.entry.allocation.extra.roots.push child ∧
          Nonempty (DuplicatePrefixBorrowAuthorization.Positive output.child.tree output.global.protectedTags
            (some child) (some child) (some output.tag) input.offset len) ∧
          GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write input.offset (input.offset+len) := by
  cases contract.reference with
  | empty zero metadata => exact False.elim (nonempty zero)
  | positive pointer encoding input =>
    have same := DuplicatePrefixSliceArgument.Argument.pointer.inj encoding
    subst pointer
    exact ⟨input,invoke_positive address len input contract.runtime contract.resources frame⟩

end
end DuplicatePrefix.S05WildcardEntryBridge
