import empty_function.InitialIndirectQuery
namespace EmptyFunction.InitialQueryTransport
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false

theorem query (s : Static) (metadata : Metadata s) (p : Packet)
    (tracker : MachineHooks.BorrowState) (destination : InputDraft.LocalDestination s p tracker)
    (old : MemPlace Provenance) (indirect : destination.oldOperand = .indirect old)
    (amount : Size) (projected : destination.offset = some amount) (after : State)
    (memory : after.machine.memory = p.before.machine.memory)
    (addresses : after.machine.user.addresses = p.before.machine.user.addresses) :
    EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers after old amount .inbounds .none =
      .ok (ProjectedIndirectPreflight.shifted old amount) := by
  rw [ProjectionSnapshot.offset_congr (ConcreteProtection.source s).pointers p.before after addresses
    (fun id => by rw [memory]) (fun id => by rw [memory])]
  exact InitialIndirectQuery.query s metadata p tracker destination old indirect amount projected
end EmptyFunction.InitialQueryTransport
