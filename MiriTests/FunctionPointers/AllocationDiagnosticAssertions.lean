import MiriTests.FunctionPointers.AllocationDiagnostics

open Miri.Memory Miri.Interpreter
private def dangling (address : UInt64) : StepError :=
  MemoryErrors.access (.danglingIntegerPointer address 0 (.dereferenceable "pointer"))

#eval show IO Unit from do
  unless dangling 0 != dangling 1 && dangling 0 != dangling 18446744073709551615 do
    throw (IO.userError "dangling pointer diagnostics collapsed distinct addresses")
