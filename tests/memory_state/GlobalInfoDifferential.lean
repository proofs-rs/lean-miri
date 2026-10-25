import Miri.Memory.MemoryState

open Miri.ABI Miri.Memory

private def idFromNat (value : Nat) : IO AllocId := do
  match AllocId.ofUInt64 (UInt64.ofNat value) with
  | some id => pure id
  | none => throw (IO.userError "test AllocId must be nonzero")

private def alignFromBytes (value : UInt64) : IO Align := do
  match Align.fromBytes value with
  | .ok align => pure align
  | .error error => throw (IO.userError (toString error))

private def allocation (mutability : Mutability := .Mut) :
    IO (Allocation Provenance Unit) := do
  match Allocation.fromBytes (Prov := Provenance) #[1, 2, 3] Align.ONE mutability with
  | .ok value => pure value
  | .error error => throw (IO.userError (toString error))

private def kindText : AllocationKind → String
  | .liveData => "liveData"
  | .function => "function"
  | .vaList => "vaList"
  | .vtable => "vtable"
  | .typeId => "typeId"
  | .dead => "dead"

private def mutabilityText : Mutability → String
  | .Not => "Not"
  | .Mut => "Mut"

private def emitInfo (state : MemoryState Provenance Unit Unit) (label : String)
    (id : AllocId) : IO Unit := do
  match state.getAllocInfo id with
  | .error _ => throw (IO.userError s!"{label}: allocation info unavailable")
  | .ok info =>
      let alignBytes := match info.align.bytes with
        | .ok bytes => bytes
        | .error _ => 0
      IO.println s!"info {label} size={info.size.bytes} align={alignBytes} kind={kindText info.kind} mut={mutabilityText info.mutability}"

def main : IO Unit := do
  let id1 ← idFromNat 1
  let id2 ← idFromNat 2
  let id3 ← idFromNat 3
  let id4 ← idFromNat 4
  let id5 ← idFromNat 5
  let id6 ← idFromNat 6
  let id7 ← idFromNat 7
  let id8 ← idFromNat 8
  let id9 ← idFromNat 9
  let id10 ← idFromNat 10
  let align2 ← alignFromBytes 2
  let align8 ← alignFromBytes 8
  let localBytes ← allocation
  let staticBytes ← allocation .Not
  let source4 ← match Allocation.fromBytes (Prov := CtfeProvenance) #[1, 2, 3]
      Align.ONE .Mut with
    | .ok value => pure value
    | .error error => throw (IO.userError (toString error))
  let .ok id1Alloc := Allocation.fromBytes (Prov := Provenance) #[1, 2, 3] Align.ONE .Mut
    | throw (IO.userError "could not create local allocation")
  let .ok id4Alloc := Allocation.fromBytes (Prov := Provenance) #[1, 2, 3] Align.ONE .Mut
    | throw (IO.userError "could not create cached global allocation")
  let empty : MemoryState Provenance Unit Unit := MemoryState.empty
  let issued := MemoryState.setIssuedIds empty #[id1, id2, id3, id4, id5, id6, id7, id8, id9]
  let globals := #[
      ⟨id4, .memory, id4Alloc.byteSize, id4Alloc.align, .Mut,
        some (.memory source4)⟩,
      ⟨id5, .static, staticBytes.byteSize, align2, .Not,
        some (.static 5 true false false)⟩,
      ⟨id6, .function, Size.ZERO, Align.ONE, .Not, some .function⟩,
      ⟨id7, .vtable, Size.ZERO, align8, .Not, some .vtable⟩,
      ⟨id8, .typeId, Size.ZERO, Align.ONE, .Not, some .typeId⟩
    ]
  let withGlobals := MemoryState.setGlobalEntries issued globals
  let withMachineIds := MemoryState.setExtraFunctionIds withGlobals #[id2]
  let withVaList := MemoryState.setVaListIds withMachineIds #[id3]
  let base : MemoryState Provenance Unit Unit := { withVaList with
    live := #[
      (id1, ⟨.stack, id1Alloc⟩),
      (id4, ⟨.machine (), id4Alloc⟩)
    ]
    dead := #[⟨id9, localBytes.byteSize, localBytes.align⟩]
  }
  emitInfo base "local" id1
  emitInfo base "extra-fn" id2
  emitInfo base "va-list" id3
  emitInfo base "cached-global" id4
  emitInfo base "global-static" id5
  emitInfo base "global-function" id6
  emitInfo base "vtable" id7
  emitInfo base "typeid" id8
  emitInfo base "dead" id9
  IO.println s!"live local={base.isAllocLive id1} extra-fn={base.isAllocLive id2} va-list={base.isAllocLive id3} global={base.isAllocLive id5} dead={base.isAllocLive id9} unknown={base.isAllocLive id10}"
