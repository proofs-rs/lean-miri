import Lean
import Miri.Input.EvalSourceRunFinalization
import Miri.Input.ExecutionChoicePolicy
import Miri.Input.NativeMathHost
import MiriTests.Connected.Proofs.ExactMap212
import MiriTests.Connected.Proofs.JsonDecidableEq213
import MiriTests.Connected.Proofs.CompilerPatternDecEq219
import MiriTests.Connected.Proofs.RuntimeDocumentExact207

open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

set_option synthInstance.maxSize 4096

namespace ExactStateCodec207
instance compilerPatternDecidableEq : DecidableEq Miri.Input.CompilerPattern :=
  PatternEquality219.compilerPatternDecEqInstance

abbrev Os := ByteArray
abbrev R := Unit
abbrev Payload := Input.EvalSyncObjectAccess.Payload
abbrev H := Unit
abbrev D := Unit
abbrev Aff := CpuAffinity.Mask
abbrev B := Unit
abbrev Poll := Unit
abbrev Instant := Unit
abbrev System := Unit
abbrev Native := Unit
abbrev Profiler := Unit
abbrev Raw := Unit
abbrev Listener := Unit
abbrev TcpStream := Unit
abbrev Error := Unit
abbrev Other := Input.EvalUnixSourceConstruction.Other Raw Listener TcpStream Error
abbrev Host := Input.EvalConfigurationCore.SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler
abbrev OuterState := MachineHooks.State MiriMemoryKind
  (ExecutionStateTransport.Outer
    (Input.EvalWorld.World Os R Payload H D Other Aff B Host))

end ExactStateCodec207

open ExactStateCodec207

namespace Miri.Memory.KeyedArray

theorem toArray_injective {K V : Type} [BEq K] [Hashable K]
    {keyFn : V → K} {left right : KeyedArray K V keyFn}
    (h : left.toArray = right.toArray) : left = right := by
  cases left
  cases right
  simp only [KeyedArray.toArray] at h
  subst_vars
  congr
  all_goals first | rfl | apply Subsingleton.elim

instance exactDecidableEq {K V : Type} [BEq K] [Hashable K]
    [DecidableEq V] {keyFn : V → K} : DecidableEq (KeyedArray K V keyFn) := by
  intro left right
  by_cases h : left.toArray = right.toArray
  · exact isTrue (toArray_injective h)
  · exact isFalse (fun equality => h (congrArg KeyedArray.toArray equality))

end Miri.Memory.KeyedArray

deriving instance DecidableEq for Miri.Memory.Allocation
deriving instance DecidableEq for Miri.Memory.GlobalAllocationPayload
deriving instance DecidableEq for Miri.Memory.LocalAllocation
deriving instance DecidableEq for Miri.Memory.GlobalAllocation
deriving instance DecidableEq for Miri.Memory.MemoryState

deriving instance DecidableEq for Miri.Concurrency.VTimestamp
deriving instance DecidableEq for Miri.Concurrency.VClock
deriving instance DecidableEq for Miri.Concurrency.ThreadClockSet
deriving instance DecidableEq for Miri.Concurrency.AtomicMemoryCellClocks
deriving instance DecidableEq for Miri.Concurrency.MemoryCellClocks
deriving instance DecidableEq for Miri.Concurrency.AllocationRanges
deriving instance DecidableEq for Miri.Concurrency.VClockAlloc
deriving instance DecidableEq for Miri.Concurrency.ThreadExtraState
deriving instance DecidableEq for Miri.Concurrency.ThreadRecord
deriving instance DecidableEq for Miri.Concurrency.ThreadManager
deriving instance DecidableEq for Miri.Concurrency.GlobalState
deriving instance DecidableEq for Miri.Concurrency.LocalRace.LocalClocks
deriving instance DecidableEq for Miri.Concurrency.LocalRace.FrameState
deriving instance DecidableEq for Miri.Interpreter.MachineHooks.CatchUnwindData
deriving instance DecidableEq for Miri.Interpreter.MachineHooks.FrameExtra
deriving instance DecidableEq for Miri.Interpreter.MachineHooks.BorrowState
deriving instance DecidableEq for Miri.Interpreter.MachineHooks.MachineState
deriving instance DecidableEq for Miri.Interpreter.StepState
deriving instance DecidableEq for Miri.Interpreter.ThreadStacks.SavedStack
deriving instance DecidableEq for Miri.Interpreter.ThreadStacks.Registry
deriving instance DecidableEq for Miri.Interpreter.ValidityMachine.Control
deriving instance DecidableEq for Miri.Interpreter.LocalsIdentitySupply
deriving instance DecidableEq for Miri.Memory.AllocAddresses.AddressRange
deriving instance DecidableEq for Miri.Memory.AllocAddresses.AddressGenerator
deriving instance DecidableEq for Miri.Memory.AllocAddresses.ReusableAddress
deriving instance DecidableEq for Miri.Memory.AllocAddresses.ReusePool
deriving instance DecidableEq for Miri.Memory.PreparedGlobalBytes
deriving instance DecidableEq for Miri.Memory.AllocAddresses.BaseAddressEntry
deriving instance DecidableEq for Miri.Memory.AllocAddresses.InverseAddressEntry
deriving instance DecidableEq for Miri.Memory.AllocAddresses.AddressGenerationState
deriving instance DecidableEq for Miri.Memory.AllocAddresses.GlobalAddressState
deriving instance DecidableEq for Miri.Interpreter.PointerMachine.User
deriving instance DecidableEq for Miri.Interpreter.ThreadStacks.Storage
deriving instance DecidableEq for Miri.Interpreter.ExecutionChoices.Input
deriving instance DecidableEq for Miri.Interpreter.ExecutionChoices.Request
deriving instance DecidableEq for Miri.Interpreter.ExecutionChoices.Event
deriving instance DecidableEq for Miri.Interpreter.ExecutionChoices.Tape
deriving instance DecidableEq for Miri.Interpreter.TlsDestructor
deriving instance DecidableEq for Miri.Interpreter.ThreadLocalEntry
deriving instance DecidableEq for Miri.Interpreter.ThreadAtexitEntry
deriving instance DecidableEq for Miri.Interpreter.TlsKeyEntry
deriving instance DecidableEq for Miri.Interpreter.ThreadTlsData
deriving instance DecidableEq for Miri.Interpreter.ThreadTlsMachine.Data
deriving instance DecidableEq for Miri.Interpreter.TlsImmediate
deriving instance DecidableEq for Miri.Interpreter.MainEntryType
deriving instance DecidableEq for Miri.Interpreter.MainThreadStage
deriving instance DecidableEq for Miri.Interpreter.GlobalCtorStage
deriving instance DecidableEq for Miri.Interpreter.FunctionPointers.FunctionEntry
deriving instance DecidableEq for Miri.Interpreter.TcpSocket.SocketState
deriving instance DecidableEq for Miri.Interpreter.IoError.HostError
deriving instance DecidableEq for Miri.Interpreter.Clock.Duration
deriving instance DecidableEq for Miri.Interpreter.TcpSocket.State
deriving instance DecidableEq for Miri.Interpreter.TlsDtorsStage
deriving instance DecidableEq for Miri.Interpreter.MainMachine.Data
deriving instance DecidableEq for Miri.Interpreter.SourceOther.Value
deriving instance DecidableEq for Miri.Interpreter.PthreadObjects.Payload
deriving instance DecidableEq for Miri.Interpreter.WindowsSync.Payload
deriving instance DecidableEq for Miri.Interpreter.MacOsSync.Unfair
deriving instance DecidableEq for Miri.Interpreter.MacOsSync.Semaphore
deriving instance DecidableEq for Miri.Interpreter.TypedSyncMetadata.Payload
deriving instance DecidableEq for Miri.Input.EvalSyncPayload.Payload
deriving instance DecidableEq for Miri.Interpreter.FunctionPointers.Registry
deriving instance DecidableEq for Miri.Interpreter.VTableMachine.Entry
deriving instance DecidableEq for Miri.Interpreter.VTableMachine.Registry
deriving instance DecidableEq for Miri.Interpreter.IntrinsicSymbolsMachine.Registry
deriving instance DecidableEq for Miri.Interpreter.ExternStatic.State
deriving instance DecidableEq for Miri.Interpreter.ThreadMachine.JoinCallback
deriving instance DecidableEq for Miri.Interpreter.ThreadMachine.Runtime
deriving instance DecidableEq for Miri.Interpreter.Unwind.PayloadStore
deriving instance DecidableEq for Miri.Interpreter.MemoryExtras.Entry
deriving instance DecidableEq for Miri.Concurrency.LoadInfo
deriving instance DecidableEq for Miri.Concurrency.StoreElement
deriving instance DecidableEq for Miri.Concurrency.StoreBuffer
deriving instance DecidableEq for Miri.Concurrency.StoreBufferAlloc
deriving instance DecidableEq for Miri.Interpreter.MemoryExtras.AllocationExtra
deriving instance DecidableEq for Miri.Interpreter.MemoryExtras.Registry
deriving instance DecidableEq for Miri.Interpreter.EnvVars.Unix
deriving instance DecidableEq for Miri.Interpreter.EnvVars.State
deriving instance DecidableEq for Miri.Interpreter.UnixDirectories.Stream
deriving instance DecidableEq for Miri.Interpreter.UnixDirectories.Table
deriving instance DecidableEq for Miri.Interpreter.Files.Description
deriving instance DecidableEq for Miri.Interpreter.Files.Ref
deriving instance DecidableEq for Miri.Interpreter.Files.WeakRef
deriving instance DecidableEq for Miri.Interpreter.Files.Table
deriving instance DecidableEq for Miri.Interpreter.FileOwnership.Entry
deriving instance DecidableEq for Miri.Interpreter.FileOwnership.Registry
deriving instance DecidableEq for Miri.Interpreter.MachineGCRoots.EntryPointers
deriving instance DecidableEq for Miri.Interpreter.MachineGCRoots.Storage
deriving instance DecidableEq for Miri.Interpreter.WindowsExitMachine.Handler
deriving instance DecidableEq for Miri.Interpreter.WindowsExitMachine.Registry
deriving instance DecidableEq for Miri.Interpreter.Clock.Instant
deriving instance DecidableEq for Miri.Interpreter.Clock.Monotonic
deriving instance DecidableEq for Miri.Interpreter.Clock.Deadline
deriving instance DecidableEq for Miri.Interpreter.BlockingIo.Source
deriving instance DecidableEq for Miri.Interpreter.BlockingIo.Manager
deriving instance DecidableEq for Miri.Interpreter.Readiness.Interest
deriving instance DecidableEq for Miri.Interpreter.Readiness.Watcher
deriving instance DecidableEq for Miri.Interpreter.Readiness.Watched
deriving instance DecidableEq for Miri.Interpreter.ReadinessMachine.WatcherEntry
deriving instance DecidableEq for Miri.Interpreter.ReadinessMachine.Registry
deriving instance DecidableEq for Miri.Concurrency.FutexRuntime.Callback
deriving instance DecidableEq for Miri.Concurrency.MutexState
deriving instance DecidableEq for Miri.Concurrency.RwLockState
deriving instance DecidableEq for Miri.Concurrency.CondvarState
deriving instance DecidableEq for Miri.Concurrency.SemaphoreState
deriving instance DecidableEq for Miri.Concurrency.FutexWaiter
deriving instance DecidableEq for Miri.Concurrency.FutexState
deriving instance DecidableEq for Miri.Concurrency.FutexRuntime.Storage
deriving instance DecidableEq for Miri.Concurrency.InitOnce.State
deriving instance DecidableEq for Miri.Concurrency.SyncRuntime.UserCapture
deriving instance DecidableEq for Miri.Concurrency.SyncRuntime.Capture
deriving instance DecidableEq for Miri.Concurrency.TypedSyncRuntime.Object
deriving instance DecidableEq for Miri.Concurrency.TypedSyncRuntime.Storage
deriving instance DecidableEq for Miri.Interpreter.EventFd.Event
deriving instance DecidableEq for Miri.Interpreter.VirtualSocket.Buffer
deriving instance DecidableEq for Miri.Interpreter.VirtualSocket.State
deriving instance DecidableEq for Miri.Interpreter.TerminatorControl.Configuration
deriving instance DecidableEq for Miri.Interpreter.TerminatorControl.Counters
deriving instance DecidableEq for Miri.Interpreter.IoCompletionData.Capture
deriving instance DecidableEq for Miri.Interpreter.OwnedSocketCompletion.Bytes
deriving instance DecidableEq for Miri.Interpreter.OwnedSocketCompletion.Accept
deriving instance DecidableEq for Miri.Interpreter.OwnedSocketCompletion.Connect
deriving instance DecidableEq for Miri.Interpreter.OwnedSocketCompletion.Peer
deriving instance DecidableEq for Miri.Interpreter.OwnedIoRuntime.Capture
deriving instance DecidableEq for Miri.Interpreter.OwnedVirtualSocket.Capture
deriving instance DecidableEq for Miri.Interpreter.OwnedTcpSocket.Action
deriving instance DecidableEq for Miri.Interpreter.OwnedTcpSocket.Capture
deriving instance DecidableEq for Miri.Interpreter.OwnedIoStore.Capture
deriving instance DecidableEq for Miri.Interpreter.OwnedIoStore.Storage
deriving instance DecidableEq for Miri.Interpreter.SourceOther.Value
deriving instance DecidableEq for Miri.Interpreter.DeadlineMachine.Registry
deriving instance DecidableEq for Miri.Interpreter.ReadinessMachine.Registry
deriving instance DecidableEq for Miri.Input.HostRuntime.Storage
deriving instance DecidableEq for Miri.Interpreter.RaceMode.Selection
deriving instance DecidableEq for Miri.Input.EvalWorld.World

#synth DecidableEq (KeyedArray UInt64 AllocId (fun (id : AllocId) => id.value))
#synth DecidableEq (MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
#synth DecidableEq (MachineHooks.MachineState MiriMemoryKind Unit)
#synth DecidableEq (BlockingIo.Manager Unit)
#synth DecidableEq (Clock.Monotonic Unit)
#synth DecidableEq (DeadlineMachine.Registry Unit Unit)
#synth DecidableEq (ReadinessMachine.Registry (Files.Ref (Files.Description Unit Unit Other)))
#synth DecidableEq (Miri.Concurrency.FutexRuntime.Storage (MPlaceTy Provenance))
#synth DecidableEq Miri.Concurrency.TypedSyncRuntime.Storage
#synth DecidableEq (OwnedIoStore.Storage (Files.Ref (Files.Description Unit Unit Other)))
#synth DecidableEq (Array (Files.FdId × EventFd.Event))
#synth DecidableEq (Array (Files.FdId × VirtualSocket.State))
#synth DecidableEq (Array (Files.FdId × Other))
#synth DecidableEq (Array (String × Unit))
#synth DecidableEq (Option Unit)
#synth DecidableEq (Miri.Input.HostRuntime.Storage Unit Unit Unit Unit Unit Other Unit Unit)
#synth DecidableEq ExactStateCodec207.OuterState

namespace ExactStateCodec207

def outerStateDecidableEq : DecidableEq OuterState := inferInstance

instance outerStateDecidableEqInstance : DecidableEq OuterState :=
  outerStateDecidableEq

#print axioms outerStateDecidableEq
#print axioms outerStateDecidableEqInstance

end ExactStateCodec207
-- Audit stable names rather than names generated from the source module path.
namespace ExactStateCodec207.Audit
private def registry : DecidableEq (DeadlineMachine.Registry Unit Unit) := inferInstance
private def storage : DecidableEq
    (Miri.Input.HostRuntime.Storage Unit Unit Unit Unit Unit Other Unit Unit) := inferInstance
private def step : DecidableEq (MachineHooks.State MiriMemoryKind Unit) := inferInstance
private def machine : DecidableEq (MachineHooks.MachineState MiriMemoryKind Unit) := inferInstance
#print registry
#print axioms registry
#print storage
#print axioms storage
#print axioms step
#print axioms machine
end ExactStateCodec207.Audit
