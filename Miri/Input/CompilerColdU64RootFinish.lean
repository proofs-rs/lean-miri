import Miri.Input.CompilerInitialAllocationStore
import Miri.Input.CompilerInitialAllocationWorld
import Miri.Input.GenericInstantiationWorld
import Miri.Interpreter.PlaceTypes
import Miri.Interpreter.CompileTime.RootFinish

/-! Bounded source interning controller over a genuinely executed allocated
u64 return place. No scalar/source-frame candidate is accepted as a root.
The caller must supply the actual completed Step return place and memory.
This module does not admit CTFE queries or claim a generic CTFE machine port.
Only pointer-free stack u64 roots are supported; machine-specific provenance
and extras are never erased for pointer-containing allocations. -/
namespace Miri.Input.CompilerColdU64RootFinish
open Miri.Memory Miri.ABI Miri.Interpreter CompilerInitialAllocation
set_option autoImplicit false
variable {E K : Type}
structure Root where
  private mk ::
  place : RuntimeStackPlace Provenance
  id : AllocId
  type : Miri.MIR.TyId

def capture (types : TypeArena.World) (place : RuntimeStackPlace Provenance)
    (resolved : ResolvedPointer ProvenanceExtra)
    (memory : MemoryState Provenance E K) : Except String Root := do
  let .memory actual := place | throw "root is not an actual allocated return place"
  let some provenance := actual.mplace.ptr.provenance | throw "allocated return root has no provenance"
  let some id := provenance.getAllocId | throw "allocated return root is wildcard"
  unless resolved.allocId == id && resolved.offset == .ZERO do
    throw "u64 root is not the resolved base of its actual allocation"
  let shape ← match ← types.lookupType actual.layout.ty with
    | .constructed value => pure (some value)
    | .material node => types.materialKey node
  unless shape == some (.integer false .u64) && actual.layout.layout.size == Size.ofBytes 8 do
    throw "allocated-root finishing supports source u64 only"
  let some (_,entry) := memory.live.find? (fun row => row.1 == id)
    | throw "executed return-place allocation is not live"
  let .stack := entry.kind | throw "executed return root is not stack storage"
  unless entry.allocation.byteSize == Size.ofBytes 8 do throw "root allocation size differs from actual return layout"
  unless entry.allocation.provenanceMap.ptrs.isEmpty &&
      entry.allocation.provenanceMap.byteFragments.isNone do
    throw "pointer-containing root needs recursive CTFE interning"
  unless entry.allocation.align == actual.layout.layout.align.abi do
    throw "root allocation alignment differs from actual return layout"
  unless entry.allocation.align.bytes == .ok 8 do throw "u64 leaf requires actual eight-byte alignment"
  pure ⟨place,id,actual.layout.ty⟩

private def restore (memory : MemoryState Provenance E K) (id : AllocId)
    (entry : LocalAllocation Provenance E K) : MemoryState Provenance E K :=
  {memory with live := (memory.live.filter (fun row => row.1 != id)).push (id,entry)}

/-- Source intern_shallow removes the real local, restores it on prepare
failure, otherwise installs the SAME identity in the global map. This is not
dedup allocation and does not create a salted-key binding. -/
def intern (target : TargetDataLayout) (root : Root) (memory : MemoryState Provenance E K) :
    Except CompileTime.RootFinish.InternError Unit × MemoryState Provenance E K := Id.run do
  let some (_,entry) := memory.live.find? (fun row => row.1 == root.id)
    | return (.error .danglingPointer,memory)
  let removed := {memory with live := memory.live.filter (fun row => row.1 != root.id)}
  let (merged,allocation) := match Allocation.provenanceMergeBytes target entry.allocation with
    | .ok merged allocation => (merged,allocation)
    | .error _ allocation => (false,allocation)
  unless merged && allocation.provenanceMap.ptrs.isEmpty && allocation.provenanceMap.byteFragments.isNone do
    return (.error .partialPointer,restore removed root.id {entry with allocation})
  let bytes := allocation.inspectWithUninitAndPtrOutsideInterpreter 0 allocation.len
  let .ok bytes := bytes | return (.error .partialPointer,restore removed root.id {entry with allocation})
  let constant := Allocation.fromCompilerSnapshot bytes allocation.align .Not
    allocation.initializationMask (ProvenanceMap.new : ProvenanceMap CtfeProvenance)
    (Size.fromBits target.pointerWidth.bits)
  let .ok constant := constant | return (.error .partialPointer,restore removed root.id {entry with allocation})
  let global : GlobalAllocation := {
    allocId := root.id,kind := .memory,size := constant.byteSize,align := constant.align,
    mutability := .Not,payload := some (.memory constant) }
  return (.ok (),removed.pushGlobal global)

private def read (target : TargetDataLayout) (root : Root) (memory : MemoryState Provenance E K) :
    Except String UInt64 := do
  let some global := memory.findGlobal? root.id | throw "interned root global absent"
  let some (.memory allocation) := global.payload | throw "interned root has no actual memory payload"
  let scalar ← (allocation.readScalar target (allocRange .ZERO (Size.ofBytes 8)) false).mapError toString
  scalar.toUInt64.mapError (fun error => reprStr error)

/-- Scalar ValTree leaf is read from the immutable actual root after intern;
no VALUE-query answer, normalized alias or MAX literal supplies these bits. -/
def readValTree (target : TargetDataLayout) (root : Root) (memory : MemoryState Provenance E K) :
    Except String (Miri.MIR.TyId × Miri.MIR.ValTree) := do
  let value ← read target root memory
  pure (root.type,⟨#[.Leaf value.toNat 8],0⟩)

def finish (target : TargetDataLayout) (root : Root) (memory : MemoryState Provenance E K) :
    Except String UInt64 × MemoryState Provenance E K :=
  match CompileTime.RootFinish.finish (intern target)
      (fun root memory => ((read target root memory).map (fun _ => ()),memory))
      (fun error memory => (s!"allocated root interning: {reprStr error}",memory))
      (fun root memory => (read target root memory,memory)) root memory with
  | .returned value memory => (value,memory)
  | .failed _ error memory => (.error error,memory)
/-- Shared-counter route: the real allocator has already consumed every raw
identity. Finishing validates the root binding and never increments a mirror.
Every error returns the actual successor memory, including intern failures. -/
def finishShared (target : TargetDataLayout) (run : Nat) (root : Root)
    (before : AllocatorWorld Provenance E K) (executed : MemoryState Provenance E K) :
    Except String UInt64 × AllocatorWorld Provenance E K := Id.run do
  let current := before.store.withMemory executed
  if executed.sourceAllocIdWorldActive then
    return (.error "prepared and initial compiler source profiles conflict",current)
  unless executed.activeInitialCompilerRun == some run do
    return (.error "allocated-root source run is not active",current)
  let some supply := executed.initialCompilerRuns.find? (fun row => row.token == run)
    | return (.error "allocated-root source supply absent",current)
  if supply.exhausted || executed.idSupplyExhausted then
    return (.error "allocated-root source supply is fatal",current)
  let some raw := executed.initialCompilerSource? run root.id
    | return (.error "allocated root lacks actual shared raw source reservation",current)
  unless executed.initialCompilerRuntime? run raw == some root.id &&
      !before.memory.hasIssuedId root.id && executed.hasIssuedId root.id do
    return (.error "allocated root reservation does not belong to this execution prefix",current)
  let (outcome,memory) := finish target root executed
  let updated := before.store.withMemory memory
  let some global := memory.findGlobal? root.id | return (outcome,updated)
  let some (.memory allocation) := global.payload | return (outcome,updated)
  let bytes ← match allocation.inspectWithUninitAndPtrOutsideInterpreter 0 allocation.len with
    | .ok bytes => pure bytes | .error error => return (.error s!"root global backing: {error}",updated)
  let alignment ← match allocation.align.bytes with
    | .ok align => pure align | .error error => return (.error s!"root global alignment: {reprStr error}",updated)
  let key : MemoryKey := {
    bytes := bytes, initMask := allocation.initializationMask, alignment := alignment, mutable := false,
    pointerBytes := (Size.fromBits target.pointerWidth.bits).bytes, littleEndian := target.endian == .little,
    provenance := allocation.provenanceMap }
  return (outcome,{updated with symbolic := updated.symbolic.push (root.id,.memory key)})
end Miri.Input.CompilerColdU64RootFinish
