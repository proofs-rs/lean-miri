import Miri.Input.AllocationImage
import Miri.Input.Decoder

/-! Actual compiler GlobalAlloc queries and shared definition identities.
Missing evidence is an error; initializer bytes do not establish declaration
mutability, foreignness or layout. -/
namespace Miri.Input.CompilerGlobals
open Miri.ABI Miri.Memory

def staticInfo (source : StaticAllocation) : Except String AllocationImage.StaticInfo := do
  let some info := source.globalInfo | throw "static global_info compiler queries are missing"
  unless info.threadLocal == source.threadLocal do throw "static TLS predicates disagree"
  unless info.isStatic do throw "GlobalAlloc::Static lacks compiler is_static evidence"
  let size ← (RuntimeMetadata.size info.sizeBytes).mapError toString
  let align ← (RuntimeMetadata.alignment info.alignBytes).mapError toString
  let mutable ← match info.mutability with
    | .mutable => pure Mutability.Mut
    | .immutable => pure Mutability.Not
  pure ⟨size, align, mutable, info.isStatic, info.foreignItem⟩

def queries : AllocationImage.Queries := ⟨staticInfo⟩

/-- Exporter definition IDs already address the complete immutable table seeded
by lowering, including statics with no selected MIR root. -/
def prepareProgram (program : LoweredProgram) : LoweredProgram := program

def importGraph [DecidableEq K] (target : RuntimeTargetDataLayout)
    (program : LoweredProgram) (initial : MemoryState P E K) : AllocationImage.ImportResult P E K :=
  let program := prepareProgram program
  AllocationImage.importGraph target program.bundle.definitions queries program.input.allocations initial

end Miri.Input.CompilerGlobals
