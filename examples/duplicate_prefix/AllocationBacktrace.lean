import Miri.Interpreter.MemoryExtras

namespace DuplicatePrefix.AllocationBacktrace
open Miri Miri.Memory Miri.Interpreter
set_option autoImplicit false

/-- Preserve the diagnostic annotation of the selected extras row. Runtime
weak-memory and synchronization conditions do not constrain this annotation. -/
def get {Payload : Type}
    (rows : Array (AllocId × MemoryExtras.AllocationExtra Payload)) (id : AllocId) :
    Option (Array (CallInstance × Miri.MIR.SpanRef)) :=
  (rows.find? (fun row => row.1 == id)).bind (fun row => row.2.backtrace)

theorem of_lookup {Payload : Type}
    {rows : Array (AllocId × MemoryExtras.AllocationExtra Payload)} {id : AllocId}
    {extra : MemoryExtras.AllocationExtra Payload}
    (present : rows.find? (fun row => row.1 == id) = some (id,extra)) :
    get rows id = extra.backtrace := by
  simp only [get,present,Option.bind_some]

end DuplicatePrefix.AllocationBacktrace
