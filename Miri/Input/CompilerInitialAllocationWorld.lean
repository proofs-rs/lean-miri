import Miri.Input.CompilerInitialAllocationSnapshot

namespace Miri.Input.CompilerInitialAllocation
open Lean Miri.Memory Miri.ABI GenericSubstitution
set_option autoImplicit false
variable {P E K : Type}
structure SourceIdentity where
  run : Nat
  raw : UInt64
  deriving DecidableEq, BEq, Repr

/-- This is the proposed complete typed dedup store extension. It cannot be
represented by the legacy byte-only/32-salt catalogue. -/
structure TypedDedup where
  run : Nat
  key : GlobalKey
  salt : UInt64
  runtime : AllocId

structure AllocatorWorld (P E K : Type) where
  memory : MemoryState P E K
  runs : Array (Nat × UInt64) := #[]
  crosswalk : Array (SourceIdentity × AllocId) := #[]
  typedDedup : Array TypedDedup := #[]
  symbolic : Array (AllocId × GlobalKey) := #[]

def runtime? (world : AllocatorWorld P E K) (run : Nat) (raw : UInt64) : Option AllocId :=
  (world.memory.initialCompilerRuntime? run raw).orElse (fun _ =>
    (world.crosswalk.find? (fun row => row.1 == ⟨run,raw⟩)).map Prod.snd)

private def allocation (world : AllocatorWorld P E K) (run : Nat) (value : MemoryKey) :
    Except String (Allocation CtfeProvenance Unit) := do
  let convert (raw : CtfeProvenance) : Except String CtfeProvenance := do
    let some target := runtime? world run raw.allocId.value | throw "reserved provenance target absent"
    (CtfeProvenance.fromParts (target,raw.immutable,raw.sharedRef)).mapError (fun e => reprStr e)
  let pointers ← value.provenance.ptrs.mapM fun (slot,raw) => do pure (slot,← convert raw)
  let fragments ← value.provenance.byteFragments.mapM fun rows => rows.mapM fun (slot,fragment) => do
    pure (slot,{fragment with prov := ← convert fragment.prov})
  let provenance ← (ProvenanceMap.fromParts pointers fragments).mapError (fun e => reprStr e)
  let align ← (Align.fromBytes value.alignment).mapError toString
  -- Checked exact constructor retains the complete optional fragment state;
  -- it does not merge Some(empty) into None or normalize mask blocks.
  (Allocation.fromCompilerSnapshot value.bytes align (if value.mutable then .Mut else .Not)
    value.initMask provenance (Size.ofBytes value.pointerBytes)).mapError toString

/-- Symbolic materialization must inspect the actual declaration/type world.
Missing capabilities return errors; no fake global metadata is synthesized. -/
structure SymbolicMaterial where
  prepare : GlobalKey → Except String GlobalAllocation
  prepareStatic : DefinitionIdentity → StaticSource → Except String GlobalAllocation := fun _ _ => .error "initial static metadata capability unavailable"

/-- Reserve every raw source identity in the prefix, including global-map holes.
That gives dangling reserved provenance an issued runtime identity without
inventing a global payload. All IDs append after existing execution IDs. -/
def install (budget : Nat) (symbolic : SymbolicMaterial) (run : Nat) (snapshot : Snapshot)
    (original : AllocatorWorld P E K) : Except String (AllocatorWorld P E K) := do
  unless snapshot.next != 0 do throw "initial snapshot frontier is zero"
  let mut previous : UInt64 := 0
  for binding in snapshot.globals do
    unless previous < binding.source && binding.source < snapshot.next do throw "invalid initial global identity"
    previous := binding.source
  let mut seen : Array DedupBinding := #[]
  for binding in snapshot.dedup do
    if seen.any (fun old => old.key == binding.key && old.salt == binding.salt) then throw "duplicate typed dedup key/salt"
    let some target := snapshot.globals.find? (·.source == binding.source) | throw "dedup target absent"
    unless target.key == binding.key do throw "dedup key differs from actual global"
    seen := seen.push binding
  if original.memory.sourceAllocIdWorldActive then throw "legacy prepared source world cannot be reinterpreted as an initial snapshot"
  if original.runs.any (fun row => row.1 == run) then throw "initial snapshot run already installed"
  let count := snapshot.next.toNat - 1
  unless count ≤ budget do throw "initial reserved-prefix installation capacity exhausted"
  let mut candidate := original
  for i in [:count] do
    let (memory,outcome) := candidate.memory.reserveInitialSnapshotSlot
    let runtime ← outcome.mapError (fun e => reprStr e)
    candidate := {candidate with memory := memory, crosswalk := candidate.crosswalk.push (⟨run,UInt64.ofNat (i+1)⟩,runtime)}
  for binding in snapshot.globals do
    let some runtime := runtime? candidate run binding.source | throw "initial global missing reserved identity"
    let entry ← match binding.key with
      | .memory image => do
        let alloc ← allocation candidate run image
        let align ← (Align.fromBytes image.alignment).mapError toString
        pure ({allocId := runtime, kind := .memory, size := Size.ofBytes (UInt64.ofNat image.bytes.size), align := align, mutability := (if image.mutable then .Mut else .Not), payload := some (.memory alloc)} : GlobalAllocation)
      | other => do
        let prepared ← match other with
          | .static definition => do
            let some info := binding.staticSource | throw "initial static source descriptor absent"
            symbolic.prepareStatic definition info
          | _ => symbolic.prepare other
        let expectedKind := match other with
          | .function _ => GlobalAllocationKind.function
          | .static _ => .static
          | .typeId _ => .typeId
          | .vtable _ _ => .vtable
          | .memory _ => .memory
        unless prepared.kind == expectedKind do throw "symbolic material kind differs from initial key"
        let validPayload := match other, prepared.payload with
          | .function _, some .function => true
          | .static _, some (.static _ _ _ _) => true
          | .typeId _, some .typeId => true
          | .vtable _ _, some .vtable => true
          | _, _ => false
        unless validPayload do throw "symbolic material payload is absent or mismatched"
        -- The resolver supplies source metadata, not an identity allocation.
        pure {prepared with allocId := runtime}
    candidate := {candidate with memory := candidate.memory.pushGlobal entry, symbolic := candidate.symbolic.push (runtime,binding.key)}
  for binding in snapshot.dedup do
    let some runtime := runtime? candidate run binding.source | throw "initial dedup target missing"
    candidate := {candidate with typedDedup := candidate.typedDedup.push ⟨run,binding.key,binding.salt,runtime⟩}
  let bindings := candidate.crosswalk.filterMap fun row =>
    if row.1.run == run then some (row.1.raw,row.2) else none
  let memory ← candidate.memory.activateInitialCompilerRun run snapshot.next bindings
  pure {candidate with memory := memory,runs := candidate.runs.push (run,snapshot.next)}

/-- A cache miss is absent capability, not a successful allocation/no-op.
Keys are compiler typed values and salts have the full u64 source domain. -/
def lookupDedup (world : AllocatorWorld P E K) (run : Nat) (key : GlobalKey) (salt : UInt64) :
    Option AllocId :=
  (world.typedDedup.find? (fun row => row.run == run && row.key == key && row.salt == salt)).map (·.runtime)

/-- Reserved map holes have a runtime identity but no GlobalAllocation entry. -/
def reservedHole (world : AllocatorWorld P E K) (run : Nat) (source : UInt64) : Bool :=
  match runtime? world run source with
  | none => false
  | some id => world.memory.hasIssuedId id && !world.memory.hasGlobalId id

/-- The caller retains the exact original value on every error, including
capacity failure after some candidate IDs have been reserved. -/
def installAtomic (budget : Nat) (symbols : SymbolicMaterial) (run : Nat) (snapshot : Snapshot)
    (original : AllocatorWorld P E K) : Except String Unit × AllocatorWorld P E K :=
  match install budget symbols run snapshot original with
  | .ok world => (.ok (),world)
  | .error error => (.error error,original)

theorem installAtomic_error (budget : Nat) (symbols : SymbolicMaterial) (run : Nat)
    (snapshot : Snapshot) (original : AllocatorWorld P E K) (error : String)
    (failed : install budget symbols run snapshot original = .error error) :
    installAtomic budget symbols run snapshot original = (.error error,original) := by
  simp only [installAtomic,failed]


end Miri.Input.CompilerInitialAllocation
