import Miri.Input.CallResolution
import Miri.Input.SourceAbiRuntime

namespace Miri.Input.CompilerInstanceAbi
open Lean Miri.ABI Miri.Interpreter
private def instanceQueries (runtime : RuntimeMetadata) :
    Array (Thunk (Except String (FnAbi MIR.TyId))) :=
  runtime.source.instances.mapIdx fun index _ =>
    Thunk.mk fun _ => SourceAbiRuntime.ofInstance runtime index #[]

structure Prepared where
  runtime : RuntimeMetadata
  program : LoweredProgram
  private instanceMemo : Array (Thunk (Except String (FnAbi MIR.TyId)))
  private instanceMemo_eq : instanceMemo = instanceQueries runtime

def prepare (runtime : RuntimeMetadata) (program : LoweredProgram) : Except String Prepared :=
  pure ⟨runtime, program, instanceQueries runtime, rfl⟩

def startSession (prepared : Prepared) (runtime : RuntimeMetadata) : Prepared :=
  ⟨runtime, prepared.program, instanceQueries runtime, rfl⟩

def abiOfInstance (prepared : Prepared) (callee : CallInstance) (extra : Array MIR.TyId) :
    Except String (FnAbi MIR.TyId) :=
  if extra.isEmpty then
    match prepared.instanceMemo[callee]? with
    | some query => query.get
    | none => SourceAbiRuntime.ofInstance prepared.runtime callee extra
  else SourceAbiRuntime.ofInstance prepared.runtime callee extra


theorem abiOfInstance_eq (prepared : Prepared) (callee : CallInstance)
    (extra : Array MIR.TyId) :
    abiOfInstance prepared callee extra =
      SourceAbiRuntime.ofInstance prepared.runtime callee extra := by
  unfold abiOfInstance
  rw [prepared.instanceMemo_eq]
  by_cases empty : extra.isEmpty
  · have equal := Array.empty_of_isEmpty empty
    subst extra
    cases entry : prepared.runtime.source.instances[callee]? <;>
      simp [instanceQueries, Array.getElem?_mapIdx, entry, Thunk.get]
  · simp [empty]


def hooks (prepared : Prepared)
    (base : CallHooks P S C E Other Extern (FnAbi MIR.TyId) (ArgAbi MIR.TyId)) :
    CallHooks P S C E Other Extern (FnAbi MIR.TyId) (ArgAbi MIR.TyId) :=
  { base with fnAbiOfInstance := fun _ callee extra =>
      match abiOfInstance prepared callee extra with
      | .ok abi => pure abi
      | .error error => throw (.invalidProgram error) }
end Miri.Input.CompilerInstanceAbi
