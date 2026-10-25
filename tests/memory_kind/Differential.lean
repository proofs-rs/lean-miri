import Miri.Memory.MiriMemoryKind
open Miri.Memory

def main : IO Unit := do
  let kinds : Array MiriMemoryKind := #[.rust, .miri, .c, .winHeap, .winLocal,
    .machine, .runtime, .global, .externStatic, .tls, .mmap, .socketAddress]
  for (kind, index) in kinds.toList.zipIdx do
    IO.println s!"{index} {kind.mayLeak} {kind.shouldSaveAllocationSpan}"
