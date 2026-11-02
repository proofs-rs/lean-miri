import Miri.Interpreter.PointerSource
import Miri.Interpreter.MemoryErrors
import Miri.Interpreter.RunLoop
namespace EmptyFunction.AddressErrorClass
open Miri Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option autoImplicit false

/-- The fixed canonical address classifier never labels an address invariant
or resource failure as Rust UB. It does not assert successful execution. -/
theorem address (error : AddressStateError) :
    RunLoop.reportsUB (PointerSource.addressError error) = false := by
  cases error <;> try rfl
  case addressGenerator reason => cases reason <;> rfl

theorem resource (message : String) : RunLoop.reportsUB (.resourceExhaustion message) = false := rfl
theorem invariant (message : String) : RunLoop.reportsUB (.invalidProgram message) = false := rfl
theorem callback (message : String) : RunLoop.reportsUB (.callback message) = false := rfl
theorem machineStop (message : String) : RunLoop.reportsUB (.machineStop message) = false := rfl

theorem allocation_oom : RunLoop.reportsUB (MemoryErrors.allocation .hostMemoryExhausted) = false := rfl

theorem cache_update (error : AllocationLookupError) :
    RunLoop.reportsUB (MemoryErrors.pointerAccess (.cacheUpdate error)) = false := rfl
end EmptyFunction.AddressErrorClass
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.AddressErrorClass.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved address error-class axiom {dependency} in {name}"
