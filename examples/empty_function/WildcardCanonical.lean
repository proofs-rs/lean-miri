import empty_function.WildcardResolution
import empty_function.ConcreteProtection

/-! Reuse the canonical resolver dictionary and preserve arbitrary actual
prefix state. This is resolution/classification, not another body interpreter. -/
namespace EmptyFunction.WildcardCanonical
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- The original raw pointer input classifies actual canonical wildcard
resolution at any prefix with the same memory and address state. No current
stack, heap shape, leaf condition or resolver-success premise is imposed. -/
theorem resolve (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (before current : State)
    (memory : current.machine.memory = before.machine.memory)
    (addresses : current.machine.user.addresses = before.machine.user.addresses)
    (tracker : MachineHooks.BorrowState) (pointer : Pointer (Option Provenance))
    (input : InputDraft.PointerInput s before tracker pointer)
    (wild : pointer.provenance = some .wildcard) :
    ∃ answer,
      s.cfg.retag.resolveAllocation pointer current = .ok answer current ∧
      TypedMemoryProviders.resolvePointer (ConcreteProtection.source s).pointers
        current.machine.memory pointer 0 current.machine =
        .ok (WildcardResolution.Encoded pointer answer) current.machine ∧
      WildcardResolution.Hits s before pointer answer := by
  obtain ⟨answer,typed,retag,hits⟩ := WildcardResolution.resolve_at s before current memory addresses
    tracker (ConcreteProtection.source s).pointers pointer input wild
    (ConcreteProtection.source_truncate s metadata.pointerSize)
  refine ⟨answer,?_,typed,hits⟩
  rw [(ConcreteProtection.bindings s metadata capacity).1]
  exact retag

end EmptyFunction.WildcardCanonical

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.Wildcard").length != 1 then
      count := count+1
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved wildcard resolver axiom: {name}: {dependency}"
  logInfo m!"Audited {count} wildcard search/resolution/canonical declarations"
