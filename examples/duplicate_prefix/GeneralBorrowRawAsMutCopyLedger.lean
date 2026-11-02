import duplicate_prefix.GeneralBorrowRawAsMutToCopy
namespace DuplicatePrefix.GeneralBorrowRawAsMutCopyLedger
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
structure Metadata (original : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : AllocId) (base offset len count : UInt64) (packet : GeneralBorrowRawAsMutToCopy.Input) : Prop where
  idEq : packet.id = id
  baseEq : packet.base = base
  offsetEq : packet.offset = offset
  lenEq : packet.len = len
  countEq : packet.count = count
  entry : packet.entry = {original with allocation := original.allocation.setExtra packet.entry.allocation.extra}
  extras : packet.machine.user.payload.payload.user.runtime.extras = before.user.payload.payload.user.runtime.extras
structure Outcome (packet : GeneralBorrowRawAsMutToCopy.Input)
    (after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) : Prop where
  addresses : after.user.addresses = packet.machine.user.addresses
  types : after.user.payload.payload.user.types = packet.machine.user.payload.payload.user.types
  extras : after.user.payload.payload.user.runtime.extras = packet.machine.user.payload.payload.user.runtime.extras
  backend : after.user.payload.payload.user.backend = .none
  ghost : after.user.payload.ghost = false
  shallow : after.user.payload.validation = .Shallow
  race : after.dataRace = none
  fixed : after.threads.fixedScheduling = true
  active : after.threads.activeThread? = some packet.thread
  unchecked : ((PreparedContracts.actualConfig packet.options () (packet.remaining+1) packet.span).terminators.getControl after.user).checkedArithmetic = false
  noGc : ((PreparedContracts.actualConfig packet.options () (packet.remaining+1) packet.span).terminators.getControl after.user).gcInterval = 0
/-- Exact actual constructor output, retained separately from physical bytes. -/
structure Resources (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (tag : BorTag)
    (packet : GeneralBorrowRawAsMutToCopy.Input) : Prop where
  treeEq : packet.entry.allocation.extra = tree
  trackerEq : packet.tracker = tracker
  tagEq : packet.tag = tag
structure Configuration (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (fuel : Nat)
    (packet : GeneralBorrowRawAsMutToCopy.Input) : Prop where
  optionsEq : packet.options = options
  limitsEq : packet.limits = limits
  remainingEq : packet.remaining = remaining
  spanEq : packet.span = span
  fuelEq : packet.fuel = fuel
end DuplicatePrefix.GeneralBorrowRawAsMutCopyLedger
