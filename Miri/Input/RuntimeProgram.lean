import Miri.Input.RuntimeMetadata
import Miri.Input.LowerMIR

/-! One owner for compiler input and its runtime layout cache. Program and
runtime views share the same input field by construction; preparation does not
compare or reparse a second JSON representation to establish that relationship. -/
namespace Miri.Input

structure RuntimeProgram where
  input : ImportDocumentCore
  bundle : LoweredBodies
  roots : Array Nat
  instances : Array (InstanceId × Nat)
  promoted : Array (Nat × Nat × Nat)
  target : ABI.RuntimeTargetDataLayout
  layouts : MIR.SharedTable (Except RuntimeMetadataError ABI.LayoutData)

@[inline] def RuntimeProgram.program (owner : RuntimeProgram) : LoweredProgram :=
  ⟨owner.bundle,owner.roots,owner.instances,owner.promoted,owner.input⟩

@[inline] def RuntimeProgram.runtime (owner : RuntimeProgram) : RuntimeMetadata :=
  ⟨owner.input,owner.target,owner.layouts⟩

/-- Replace the lowered view while keeping its compiler source and layout
cache fixed. Identity-appending preparation uses this operation. -/
def RuntimeProgram.withProgram (owner : RuntimeProgram) (program : LoweredProgram) : RuntimeProgram :=
  {owner with
    bundle := program.bundle
    roots := program.roots
    instances := program.instances
    promoted := program.promoted}

/-- Runtime-only clients need no lowered body view. -/
def RuntimeProgram.ofRuntime (runtime : RuntimeMetadata) : RuntimeProgram := {
  input := runtime.source
  bundle := ⟨#[],runtime.source.mirTables.compiler.spans,
    runtime.source.mirTables.compiler.definitions,runtime.source.mirTables.compiler.typeConstants⟩
  roots := #[]
  instances := #[]
  promoted := #[]
  target := runtime.target
  layouts := runtime.layouts }

def RuntimeProgram.ofProgram (program : LoweredProgram) : Except String RuntimeProgram := do
  let runtime ← (RuntimeMetadata.ofDocument program.input).mapError toString
  return (RuntimeProgram.ofRuntime runtime).withProgram program

end Miri.Input
