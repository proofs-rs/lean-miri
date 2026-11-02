import duplicate_prefix.OrdinaryAddressCacheFormation
import Miri.Input.EvalAllocationMachine

namespace DuplicatePrefix.ProductionAddressOrigin
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
-- Branch-uniform reduction lists intentionally contain case-specific rules.
set_option linter.unusedSimpArgs false

/-- A returned ready address has the exact coherent base row. Errors and
pending clock acquisition are retained as such, not asserted successful. -/
def ReadyOrigin (id : AllocId) (result : AddressStateResult AddressAssignment) : Prop :=
  match result.outcome with
  | .ok (.ready base) =>
    result.state.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩
  | .ok (.acquireRequired pendingId _ _) => pendingId = id
  | .error _ => True

private theorem cache_origin (addresses : GlobalAddressState) (id : AllocId) (base : UInt64) :
    match (addresses.cacheAddress id base).outcome with
    | .ok _ => (addresses.cacheAddress id base).state.baseAddr.find?
        (fun row => row.allocId == id) = some ⟨id, base⟩
    | .error _ => True := by
  cases cached : addresses.baseAddr.find? (fun row => row.allocId == id) with
  | none =>
    have formed := OrdinaryAddressCacheFormation.registered_base addresses id base cached
    cases (addresses.cacheAddress id base).outcome <;> simp_all
  | some row =>
    unfold GlobalAddressState.cacheAddress
    unfold_internal ".GlobalAddressState.findBase"
    simp only [cached, Option.map_some]
    trivial

private theorem returned_origin (addresses : GlobalAddressState) (id : AllocId) (base : UInt64) :
    ReadyOrigin id (match (addresses.cacheAddress id base).outcome with
      | .ok _ => (show AddressStateResult AddressAssignment from
          ⟨(addresses.cacheAddress id base).state, .ok (.ready base)⟩)
      | .error error => (show AddressStateResult AddressAssignment from
          ⟨(addresses.cacheAddress id base).state, .error error⟩)) := by
  have source := cache_origin addresses id base
  cases outcome : (addresses.cacheAddress id base).outcome with
  | error error => trivial
  | ok value => simpa only [outcome, ReadyOrigin] using source

/-- Uniform origin theorem for the actual raw source address algorithm.
Existing, reuse, no-reuse, native, type-ID and error branches are all included;
no particular allocator choice or successful outcome is supplied as a premise. -/
theorem assignment_origin (addresses : GlobalAddressState) (id : AllocId)
    (info : Option AllocationAddressInfo) (choices : AddressRandomChoices)
    (hooks : AddressExternalHooks) :
    ReadyOrigin id (addresses.addrFromAllocId id info choices hooks) := by
  cases cached : addresses.baseAddr.find? (fun row => row.allocId == id) with
  | some row =>
    have identity : row.allocId = id := by simpa using Array.find?_some cached
    have shape : row = (⟨id, row.address⟩ : BaseAddressEntry) := by cases row; simp_all
    unfold GlobalAddressState.addrFromAllocId
    unfold_internal ".GlobalAddressState.findBase"
    simp only [cached, Option.map_some]
    exact cached.trans (congrArg some shape)
  | none =>
    unfold GlobalAddressState.addrFromAllocId
    unfold_internal ".GlobalAddressState.findBase"
    unfold_internal ".GlobalAddressState.setGeneration"
    simp only [cached, Option.map_none]
    dsimp only [Id.run, bind, pure]
    repeat' first
      | exact returned_origin _ id _
      | trivial
      | split

/-- Origin postcondition of a completed actual pointer-machine address call.
No assertion of successful execution is made in its error branch. -/
def MachineOrigin {K U : Type} (id : AllocId)
    (result : EStateM.Result StepError (PointerMachine.State K U) UInt64) : Prop :=
  match result with
  | .ok base next => next.machine.user.addresses.baseAddr.find?
      (fun row => row.allocId == id) = some ⟨id, base⟩
  | .error _ _ => True

theorem pointer_machine_origin {K U : Type}
    (h : PointerMachine.Hooks K U) (id : AllocId) (kind : Option AddressMemoryKind)
    (choices : AddressRandomChoices) (before : PointerMachine.State K U) :
    MachineOrigin id (PointerMachine.addrFromAllocId h id kind choices before) := by
  cases cached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) with
  | some row =>
    have identity : row.allocId = id := by simpa using Array.find?_some cached
    have shape : row = (⟨id, row.address⟩ : BaseAddressEntry) := by cases row; simp_all
    unfold PointerMachine.addrFromAllocId
    unfold_internal ".PointerMachine.addresses"
    simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure, cached, MachineOrigin]
    exact congrArg some shape
  | none =>
    unfold PointerMachine.addrFromAllocId
    unfold_internal ".PointerMachine.addresses"
    unfold_internal ".PointerMachine.finish"
    unfold_internal ".PointerMachine.setAddresses"
    simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, cached]
    split
    · rename_i selectedKind
      simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
        pure, Pure.pure, EStateM.pure]
      cases metadata : before.machine.memory.getAllocInfo id with
      | error error =>
        simp only [metadata, MachineOrigin, throw, throwThe, MonadExceptOf.throw, EStateM.throw, bind, Bind.bind, EStateM.bind]
      | ok info =>
        simp only [metadata, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
          pure, Pure.pure, EStateM.pure]
        generalize classification : (if info.kind == .dead then AllocationAddressKind.dead
          else if info.kind == .typeId then .typeId else .liveData) = addressClass
        split
        · cases external : h.externalAddress id
            {kind := addressClass, live := before.machine.memory.isAllocLive id,
              size := info.size, align := info.align, memoryKind := some selectedKind,
              thread := UInt32.ofNat before.machine.threads.activeThread.toNat} before with
          | error error after =>
            simp only [external, bind, Bind.bind, EStateM.bind, MachineOrigin]
          | ok base after =>
            simp only [external, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
              pure, Pure.pure, EStateM.pure]
            let pending := after.machine.user.addresses.addrFromAllocId id
              (some {kind := addressClass, live := before.machine.memory.isAllocLive id, size := info.size,
                     align := info.align, memoryKind := some selectedKind,
                     thread := UInt32.ofNat before.machine.threads.activeThread.toNat}) choices ⟨some base⟩
            have origin := assignment_origin after.machine.user.addresses id
              (some {kind := addressClass, live := before.machine.memory.isAllocLive id, size := info.size,
                     align := info.align, memoryKind := some selectedKind,
                     thread := UInt32.ofNat before.machine.threads.activeThread.toNat}) choices ⟨some base⟩
            change ReadyOrigin id pending at origin
            cases outcome : pending.outcome with
            | error error =>
              dsimp only [pending] at outcome
              simp only [outcome, MachineOrigin, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
            | ok assignment =>
              cases assignment with
              | ready address =>
                have own : pending.state.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,address⟩ := by
                  simpa only [ReadyOrigin, outcome] using origin
                dsimp only [pending] at outcome own
                simpa only [outcome, MachineOrigin, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw, EStateM.throw] using own
              | acquireRequired requested address clock =>
                have same : requested = id := by simpa only [ReadyOrigin, outcome] using origin
                subst requested
                have cached := cache_origin pending.state id address
                dsimp only [pending] at outcome cached
                simp only [outcome, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
                cases race : after.machine.dataRace with
                | none =>
                  simp only [race, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
                  cases cacheResult : (pending.state.cacheAddress id address).outcome <;>
                    first
                    | solve | simp only [pending, cacheResult, MachineOrigin, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
                    | simpa only [pending, cacheResult, MachineOrigin, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw, EStateM.throw] using cached
                | some global =>
                  simp only [race]
                  cases acquired : global.acquireClock after.machine.threads clock with
                  | error error =>
                    simp only [acquired, MachineOrigin, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
                  | ok global =>
                    simp only [acquired, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
                    cases cacheResult : (pending.state.cacheAddress id address).outcome <;>
                      first
                      | solve | simp only [pending, cacheResult, MachineOrigin, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
                      | simpa only [pending, cacheResult, MachineOrigin, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw, EStateM.throw] using cached
        · simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
            pure, Pure.pure, EStateM.pure]
          let pending := before.machine.user.addresses.addrFromAllocId id
            (some {kind := addressClass, live := before.machine.memory.isAllocLive id, size := info.size,
                   align := info.align, memoryKind := some selectedKind,
                   thread := UInt32.ofNat before.machine.threads.activeThread.toNat}) choices ⟨none⟩
          have origin := assignment_origin before.machine.user.addresses id
            (some {kind := addressClass, live := before.machine.memory.isAllocLive id, size := info.size,
                   align := info.align, memoryKind := some selectedKind,
                   thread := UInt32.ofNat before.machine.threads.activeThread.toNat}) choices ⟨none⟩
          change ReadyOrigin id pending at origin
          cases outcome : pending.outcome with
          | error error =>
            dsimp only [pending] at outcome
            simp only [outcome, MachineOrigin, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
          | ok assignment =>
            cases assignment with
            | ready address =>
              have own : pending.state.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,address⟩ := by
                simpa only [ReadyOrigin, outcome] using origin
              dsimp only [pending] at outcome own
              simpa only [outcome, MachineOrigin, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw, EStateM.throw] using own
            | acquireRequired requested address clock =>
              have same : requested = id := by simpa only [ReadyOrigin, outcome] using origin
              subst requested
              have cached := cache_origin pending.state id address
              dsimp only [pending] at outcome cached
              simp only [outcome, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
              cases race : before.machine.dataRace with
              | none =>
                simp only [race, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
                cases cacheResult : (pending.state.cacheAddress id address).outcome <;>
                  first
                  | solve | simp only [pending, cacheResult, MachineOrigin, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
                  | simpa only [pending, cacheResult, MachineOrigin, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw, EStateM.throw] using cached
              | some global =>
                simp only [race]
                cases acquired : global.acquireClock before.machine.threads clock with
                | error error =>
                  simp only [acquired, MachineOrigin, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
                | ok global =>
                  simp only [acquired, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
                  cases cacheResult : (pending.state.cacheAddress id address).outcome <;>
                    first
                    | solve | simp only [pending, cacheResult, MachineOrigin, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
                    | simpa only [pending, cacheResult, MachineOrigin, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw, EStateM.throw] using cached
    · trivial

private theorem bind_origin {K U A : Type} (id : AllocId)
    (action : PointerMachine.M K U A) (next : A → PointerMachine.M K U UInt64)
    (origin : ∀ value state, MachineOrigin id (next value state))
    (before : PointerMachine.State K U) :
    MachineOrigin id ((action >>= next) before) := by
  cases ran : action before with
  | error error after => simp only [bind, Bind.bind, EStateM.bind, ran, MachineOrigin]
  | ok value after => simpa only [bind, Bind.bind, EStateM.bind, ran] using origin value after

/-- Actual production tape-based address origin. Every tape result and source
choice branch is quantified; errors do not become successful pointer origins.
No existing cache or successful address operation is assumed. -/
theorem execution_origin {K U : Type}
    (access : ExecutionChoices.Access (PointerMachine.State K U))
    (h : PointerMachine.Hooks K U) (id : AllocId) (kind : Option AddressMemoryKind)
    (before : PointerMachine.State K U) :
    MachineOrigin id (ExecutionAddressChoices.addrFromAllocId access h id kind before) := by
  cases cached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) with
  | some row =>
    have identity : row.allocId = id := by simpa using Array.find?_some cached
    have shape : row = (⟨id, row.address⟩ : BaseAddressEntry) := by cases row; simp_all
    unfold ExecutionAddressChoices.addrFromAllocId
    simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure, cached, MachineOrigin]
    exact congrArg some shape
  | none =>
    unfold ExecutionAddressChoices.addrFromAllocId
    cases kind with
    | none =>
      simp only [cached, MachineOrigin, get, getThe, MonadStateOf.get, EStateM.get,
        bind, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
    | some kind =>
      simp only [cached, get, getThe, MonadStateOf.get, EStateM.get,
        bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
      cases metadata : before.machine.memory.getAllocInfo id with
      | error error =>
        simp only [metadata, MachineOrigin, get, getThe, MonadStateOf.get, EStateM.get,
          bind, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
      | ok info =>
        simp only [metadata, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
        split
        · trivial
        · split
          · exact pointer_machine_origin h id (some kind) _ before
          · cases generationEq : before.machine.user.addresses.generation with
            | none =>
              simp only [generationEq, MachineOrigin, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
            | some generation =>
              simp only [generationEq]
              split
              all_goals
                apply bind_origin id
                intro reuse afterReuse
                split
              all_goals
                apply bind_origin id
                intro cross afterCross
                apply bind_origin id
                intro sampled afterRead
                apply bind_origin id
                intro installed afterInstall
                cases prepared : (generation.reusePool.prepareTakeAddr reuse cross info.size info.align kind
                    (UInt32.ofNat sampled.machine.threads.activeThread.toNat)).outcome with
                | error error =>
                  simp only [prepared, MachineOrigin, bind, Bind.bind, EStateM.bind,
                    throw, throwThe, MonadExceptOf.throw, EStateM.throw]
                | ok range =>
                  simp only [prepared, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
                  cases range with
                  | none =>
                    dsimp only
                    apply bind_origin id
                    intro selected afterChoice
                    simp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
                    exact pointer_machine_origin h id (some kind) _ afterChoice
                  | some range =>
                    cases range with
                    | mk start stop =>
                      dsimp only
                      apply bind_origin id
                      intro selected afterChoice
                      simp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
                      exact pointer_machine_origin h id (some kind) _ afterChoice

/-- Origin of the actual concrete pointer value, rather than just its address. -/
def PointerOrigin {K U : Type} (id : AllocId) (tag : BorTag)
    (result : EStateM.Result StepError (PointerMachine.State K U) (Pointer Provenance)) : Prop :=
  match result with
  | .ok pointer next => ∃ base,
      next.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩ ∧
      pointer = Pointer.new (Provenance.concrete id tag) (Size.ofBytes base)
  | .error _ _ => True

private theorem map_pointer_origin {K U : Type} (id : AllocId) (tag : BorTag)
    (action : PointerMachine.M K U UInt64) (before : PointerMachine.State K U)
    (origin : MachineOrigin id (action before)) :
    PointerOrigin id tag ((do
      let base ← action
      pure (Pointer.new (Provenance.concrete id tag) (Size.ofBytes base))) before) := by
  cases returned : action before with
  | error error after => simp only [bind, Bind.bind, EStateM.bind, returned, PointerOrigin]
  | ok base after =>
    have cached : after.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
        some ⟨id, base⟩ := by simpa only [returned, MachineOrigin] using origin
    simp only [bind, Bind.bind, EStateM.bind, returned, pure, Pure.pure, EStateM.pure, PointerOrigin]
    exact ⟨base, cached, rfl⟩

/-- Actual configured allocation root-pointer creation supplies cachedBase for
its returned pointer, for arbitrary live rows and tape/allocator outcomes.
This is a local origin postcondition, not proof of all callers' provenance. -/
theorem allocation_root_origin {Os R P H D O Aff B Host : Type}
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (ThreadStacks.Storage (Input.EvalWorld.World Os R P H D O Aff B Host))))
    (extras : MemoryExtras.Hooks MiriMemoryKind (Input.EvalAllocationMachine.User Os R P H D O Aff B Host) P)
    (config : PlaceMachine.AllocationConfig MiriMemoryKind (Input.EvalAllocationMachine.User Os R P H D O Aff B Host))
    (id : AllocId) (tag : BorTag)
    (before : Input.EvalAllocationMachine.State Os R P H D O Aff B Host) :
    PointerOrigin id tag ((Input.EvalAllocationMachine.allocation pointers extras config).adjustRootAddress
      id tag before) := by
  unfold Input.EvalAllocationMachine.allocation
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind]
  cases selected : ((before.machine.memory.live.map fun (id, entry) =>
      (id, entry.1, entry.2)).find? (fun entry => entry.1 == id)) with
  | none =>
    simp only [selected, PointerOrigin, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  | some row =>
    rcases row with ⟨selectedId, kind, allocation⟩
    simp only [selected]
    apply map_pointer_origin id tag _ before
    exact execution_origin Input.EvalAllocationMachine.tape pointers id _ before

end DuplicatePrefix.ProductionAddressOrigin
