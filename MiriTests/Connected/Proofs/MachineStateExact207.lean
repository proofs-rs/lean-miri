import Lean
import Miri.Input.EvalSourceRunFinalization
import Miri.Input.ExecutionChoicePolicy
import Miri.Input.NativeMathHost

open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

private abbrev Os := ByteArray
private abbrev R := Unit
private abbrev Payload := Input.EvalSyncObjectAccess.Payload
private abbrev H := Unit
private abbrev D := Unit
private abbrev Aff := CpuAffinity.Mask
private abbrev B := Unit
private abbrev Poll := Unit
private abbrev Instant := Unit
private abbrev System := Unit
private abbrev Native := Unit
private abbrev Profiler := Unit
private abbrev Raw := Unit
private abbrev Listener := Unit
private abbrev TcpStream := Unit
private abbrev Error := Unit
private abbrev Other := Input.EvalUnixSourceConstruction.Other Raw Listener TcpStream Error
private abbrev Host := Input.EvalConfigurationCore.SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler
private abbrev OuterState := MachineHooks.State MiriMemoryKind
  (ExecutionStateTransport.Outer
    (Input.EvalWorld.World Os R Payload H D Other Aff B Host))

namespace MiriTests.MachineStateExact207

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

#synth DecidableEq (MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
#synth DecidableEq (MachineHooks.MachineState MiriMemoryKind Unit)
#synth DecidableEq (MachineHooks.State MiriMemoryKind Unit)
#print axioms MiriTests.MachineStateExact207.toArray_injective
-- Keep diagnostic references independent of Lean's generated instance names.
namespace Audit
private def memory : DecidableEq
    (MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind) := inferInstance
private def machine : DecidableEq (MachineHooks.MachineState MiriMemoryKind Unit) := inferInstance
private def step : DecidableEq (MachineHooks.State MiriMemoryKind Unit) := inferInstance
#print axioms memory
#print axioms machine
#print axioms step
end Audit
end MiriTests.MachineStateExact207
