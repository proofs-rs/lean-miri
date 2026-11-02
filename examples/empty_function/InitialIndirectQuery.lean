import empty_function.ReturnGeometry
namespace EmptyFunction.InitialIndirectQuery
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The original local's raw pointer and extent determine its actual offset
query; no later materialization or resource-success premise is used. -/
theorem query (s : Static) (metadata : Metadata s) (p : Packet)
    (tracker : MachineHooks.BorrowState) (destination : InputDraft.LocalDestination s p tracker)
    (old : MemPlace Provenance) (indirect : destination.oldOperand = .indirect old)
    (amount : Size) (projected : destination.offset = some amount) :
    EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers p.before old amount .inbounds .none =
      .ok (ProjectedIndirectPreflight.shifted old amount) := by
  by_cases zero : amount.bytes = 0
  · have same : amount = Size.ZERO := by cases amount;cases zero;rfl
    rw [same]
    simpa [ProjectedIndirectPreflight.shifted,Size.ZERO,Size.ofBytes] using
      ProjectionZero.source s metadata p.before old
  · have within : amount.bytes.toNat ≤ destination.baseLayout.layout.size.bytes.toNat := by
      cases destination
      cases projected
      assumption
    have parentPositive : destination.baseLayout.layout.size.bytes ≠ 0 := by
      intro empty
      have positive : 0 < amount.bytes.toNat := by
        have ne : amount.bytes.toNat ≠ 0 := by intro eq;apply zero;exact UInt64.toNat_inj.mp eq
        omega
      rw [empty] at within
      simp only [UInt64.toNat_zero] at within
      omega
    obtain ⟨foot⟩ := destination.oldFootprint (by rw [projected];rfl) parentPositive old indirect
    have tables : old.ptr.provenance = some .wildcard → InputDraft.AddressTables p.before := by
      intro wild
      cases destination.oldPointer old indirect with
      | integer encoding => rw [encoding] at wild;cases wild
      | concrete id tag base table encoding cached backing parent latentRoot => exact table
      | wildcard encoding mode table selected => exact table
    exact IndirectProjection.positive s metadata p.before old destination.baseLayout.layout.size amount
      foot tables zero within destination.baseSigned

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``query) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved raw initial query axiom {dependency}"
#print axioms query
end EmptyFunction.InitialIndirectQuery
