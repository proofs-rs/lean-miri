import MiriTests.Connected.Proofs.ExactStateCodec207

open Lean Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option synthInstance.maxSize 4096

namespace ExactEqualityFast225
open ExactStateCodec207

local instance jsonDecEq : DecidableEq Json := ExactJson213.jsonDecidableEq
local instance patternDecEq : DecidableEq Input.CompilerPattern := ExactStateCodec207.compilerPatternDecidableEq

def importDocumentCorePointerDecEq : DecidableEq Input.ImportDocumentCore :=
  fun left right => withPtrEqDecEq left right (fun _ =>
    Miri.Verification.RuntimeDocumentExact207.instDecidableEqImportDocumentCore_miriTests left right)

attribute [-instance] Miri.Verification.RuntimeDocumentExact207.instDecidableEqRuntimeMetadata_miriTests
local instance importDocumentCoreFast : DecidableEq Input.ImportDocumentCore := importDocumentCorePointerDecEq
deriving instance DecidableEq for Input.RuntimeMetadata
private def runtimeMetadataStructuralDecEq : DecidableEq Input.RuntimeMetadata := inferInstance
def runtimeMetadataPointerDecEq : DecidableEq Input.RuntimeMetadata :=
  fun left right => withPtrEqDecEq left right (fun _ => runtimeMetadataStructuralDecEq left right)

attribute [-instance] Miri.Verification.RuntimeDocumentExact207.instDecidableEqWorld_miriTests
local instance runtimeMetadataFast : DecidableEq Input.RuntimeMetadata := runtimeMetadataPointerDecEq
deriving instance DecidableEq for Input.RuntimeArrayTypes.World
private def runtimeArrayWorldStructuralDecEq : DecidableEq Input.RuntimeArrayTypes.World := inferInstance
def runtimeArrayWorldPointerDecEq : DecidableEq Input.RuntimeArrayTypes.World :=
  fun left right => withPtrEqDecEq left right (fun _ => runtimeArrayWorldStructuralDecEq left right)

attribute [-instance] instDecidableEqWorld_miriTests
local instance runtimeArrayWorldFast : DecidableEq Input.RuntimeArrayTypes.World := runtimeArrayWorldPointerDecEq
deriving instance DecidableEq for Input.EvalWorld.World

/- The exact state comparator visits `MachineState.memory` before clocks and
threads. Wrap that large field's actual structural decision procedure before
rebuilding the generic MachineState instance below. The fallback is the frozen
207 field-by-field comparator, so this only skips unchanged shared memories. -/
attribute [-instance] instDecidableEqMemoryState_miriTests
instance memoryStatePointerDecEq {Prov Extra MachineKind : Type}
    [DecidableEq Prov] [DecidableEq Extra] [DecidableEq MachineKind] :
    DecidableEq (MemoryState Prov Extra MachineKind) :=
  fun left right => withPtrEqDecEq left right (fun _ =>
    instDecidableEqMemoryState_miriTests left right)

attribute [-instance] instDecidableEqMachineState_miriTests
deriving instance DecidableEq for MachineHooks.MachineState

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
abbrev CoreWorld := Input.EvalWorld.World Os R Payload H D Other Aff B Host
abbrev UserStack := ExecutionStateTransport.Outer CoreWorld
abbrev ConcreteMemory := MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
abbrev ConcreteMachine := MachineHooks.MachineState MiriMemoryKind UserStack
abbrev OuterState := MachineHooks.State MiriMemoryKind UserStack

attribute [-instance] ExactStateCodec207.outerStateDecidableEqInstance
private def concreteMemoryDecEq : DecidableEq ConcreteMemory := inferInstance
private def concreteMachineStructuralDecEq : DecidableEq ConcreteMachine := inferInstance

def concreteMachinePointerDecEq : DecidableEq ConcreteMachine :=
  fun left right => withPtrEqDecEq left right (fun _ => concreteMachineStructuralDecEq left right)
local instance concreteMachineFast : DecidableEq ConcreteMachine := concreteMachinePointerDecEq

def outerStateDecidableEqFast : DecidableEq OuterState := inferInstance

#synth DecidableEq CoreWorld
#synth DecidableEq ConcreteMemory
#synth DecidableEq ConcreteMachine
#synth DecidableEq OuterState

#print axioms importDocumentCorePointerDecEq
#print axioms runtimeMetadataPointerDecEq
#print axioms runtimeArrayWorldPointerDecEq
#print axioms memoryStatePointerDecEq
#print axioms concreteMachinePointerDecEq
#print axioms outerStateDecidableEqFast

end ExactEqualityFast225
