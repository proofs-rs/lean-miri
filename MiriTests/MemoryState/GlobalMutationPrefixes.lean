import Miri.Memory.MemoryState

/-! Regression for the pre22 dual-memory bug. These are executable lifecycle
assertions, not MIR execution or source equivalence certification. The nested
callback uses the actual global registration/ID supply, including on failure. -/
open Miri.ABI Miri.Memory
private abbrev Mem := MemoryState Provenance Unit Unit
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def must (value : Except ε A) : IO A :=
  match value with | .ok value => pure value | .error _ => throw (IO.userError "fixture construction failed")
private def hooks (source : Allocation CtfeProvenance Unit)
    (runtime : Allocation Provenance Unit) (owned fail : Bool) :
    GlobalAllocationHooks Provenance Unit Unit (Array String) where
  synchronizeMemory := fun _ state => state
  evaluateStaticInitializer := fun memory state _ => ⟨memory,state,.ok source⟩
  beforeAccessGlobal := fun memory state _ _ _ _ => ⟨memory,state.push "before",.ok ()⟩
  adjustGlobalAllocation := fun memory state _ _ => Id.run do
    let nested := MemoryLifecycle.registerImportedGlobal memory (state.push "nested")
      22 .memory runtime.byteSize runtime.align .Mut (some (.memory source))
    let id ← match nested.outcome with
      | .ok id => pure id
      | .error _ => return ⟨nested.memory,nested.hooks,.error "nested registration failed"⟩
    let state := nested.hooks.push s!"reserved:{id.value}"
    if fail then return ⟨nested.memory,state,.error "after nested reservation"⟩
    return ⟨nested.memory,state,.ok (if owned then .owned runtime else .borrowed runtime)⟩
private def retained (memory : Mem) (state : Array String) (outer nested : AllocId) : IO Unit := do
  check (memory.issuedIds == #[outer,nested] && memory.nextAllocId == 3)
    "nested reservation or consumed ID prefix lost"
  check (memory.runtimeIdForExport? 22 == some nested && memory.globals.any (·.allocId == nested))
    "nested global registration lost"
  check (state == #["before","nested",s!"reserved:{nested.value}"])
    "hook event prefix lost"
  let (after,reservation) := memory.reserveAllocId
  let next ← must reservation
  check (next.value == 3 && after.issuedIds.size == 3)
    "subsequent reservation reused nested identity"

def main : IO Unit := do
  let source ← must (Allocation.fromBytes (Prov := CtfeProvenance) #[4,5,6] Align.ONE .Not)
  let runtime ← must (Allocation.fromBytes (Prov := Provenance) #[4,5,6] Align.ONE .Mut)
  let initial := MemoryLifecycle.registerImportedGlobal (MemoryState.empty : Mem) (#[] : Array String)
    11 .memory source.byteSize source.align .Not (some (.memory source))
  let outer ← must initial.outcome
  let some nested := AllocId.ofUInt64 2 | throw (IO.userError "nested id invalid")
  for owned in [false,true] do
    let success := MemoryLifecycle.getAllocRaw initial.memory #[] outer (some ()) (hooks source runtime owned false)
    let _ ← must success.outcome
    retained success.memory success.hooks outer nested
    check ((success.memory.live.any (·.1 == outer)) == owned)
      "owned cache insertion or borrowed noninsertion changed"
  let failed := MemoryLifecycle.getAllocRaw initial.memory #[] outer (some ()) (hooks source runtime true true)
  check (failed.outcome matches .error (.globalAccess (.hookFailure "adjustGlobalAllocation" "after nested reservation")))
    "adjustment failure changed category"
  retained failed.memory failed.hooks outer nested
  check (!(failed.memory.live.any (·.1 == outer))) "failed adjustment cached outer allocation"
  let immutable ← must (Allocation.fromBytes (Prov := Provenance) #[4,5,6] Align.ONE .Not)
  let readonly := MemoryLifecycle.getAllocRawMut initial.memory #[] outer (some ()) (hooks source immutable true false)
  check (readonly.outcome matches .error (.readOnlyAllocation _)) "immutable write unexpectedly succeeded"
  retained readonly.memory readonly.hooks outer nested
  check (readonly.memory.live.any (·.1 == outer)) "readonly error lost completed outer materialization"
  let failedWrite := MemoryLifecycle.getAllocRawMut initial.memory #[] outer (some ()) (hooks source runtime true true)
  check (failedWrite.outcome matches .error (.globalAccess (.hookFailure "adjustGlobalAllocation" "after nested reservation")))
    "write adjustment failure changed category"
  retained failedWrite.memory failedWrite.hooks outer nested
  -- Embedded-memory hook state must see the cache inserted after callbacks.
  let coherent : GlobalAllocationHooks Provenance Unit Unit Mem := {
    synchronizeMemory := fun memory _ => memory
    evaluateStaticInitializer := fun memory _ _ => ⟨memory,memory,.ok source⟩
    beforeAccessGlobal := fun memory _ _ _ _ _ => ⟨memory,memory,.ok ()⟩
    adjustGlobalAllocation := fun memory _ _ _ =>
      let registered := MemoryLifecycle.registerImportedGlobal memory () 22 .memory
        source.byteSize source.align .Not (some (.memory source))
      match registered.outcome with
      | .error _ => ⟨registered.memory,registered.memory,.error "registration failed"⟩
      | .ok _ => ⟨registered.memory,registered.memory,.ok (.owned immutable)⟩ }
  let synced := MemoryLifecycle.getAllocRawMut initial.memory initial.memory outer (some ()) coherent
  check (synced.outcome matches .error (.readOnlyAllocation _)) "coherence readonly error missing"
  check (synced.hooks.issuedIds == synced.memory.issuedIds &&
      synced.hooks.runtimeIdForExport? 22 == some nested &&
      synced.hooks.live.any (·.1 == outer))
    "returned hook state lost nested reservation or outer cache synchronization"
  IO.println "global mutation prefixes: nested registration and ID supply retained across borrowed/owned success, adjustment failures, and readonly error"
