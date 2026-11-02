import empty_function.AddressErrorClass
import empty_function.RelocationByteActual
import empty_function.ChoiceExecution
import Miri.Interpreter.MachineAddress
namespace EmptyFunction.MachineAddressPartial
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open MachineAddress
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
def NonUBResult {S A : Type} (result : EStateM.Result StepError S A) : Prop :=
  match result with
  | .ok _ _ => True
  | .error error _ => RunLoop.reportsUB error = false

theorem assign {K U : Type} (h : Hooks K U) (state : State K U)
    (id : AllocId) (kind : Option AddressMemoryKind) (choices : AddressRandomChoices)
    (managed : state.user.addresses.addressMode = .managed)
    (noRace : state.dataRace = none)
    (classifier : h.classifyAddressError = PointerSource.addressError) :
    NonUBResult (MachineAddress.assign h id kind choices state) := by
  cases cache : state.user.addresses.baseAddr.find? (fun row => row.allocId == id) with
  | some cached =>
    unfold MachineAddress.assign
    unfold_machine_address_helpers
    simp [cache,get,getThe,MonadStateOf.get,EStateM.get,
      bind,EStateM.bind,pure,EStateM.pure,NonUBResult]
  | none =>
    cases kind with
    | none =>
      unfold MachineAddress.assign
      unfold_machine_address_helpers
      simp [cache,get,getThe,MonadStateOf.get,EStateM.get,
        bind,EStateM.bind,pure,EStateM.pure,NonUBResult,
        throw,throwThe,MonadExceptOf.throw,EStateM.throw,NonUBResult,classifier,AddressErrorClass.address,AddressErrorClass.callback]
    | some kind =>
      cases metadata : state.memory.getAllocInfo id with
      | error error =>
        unfold MachineAddress.assign
        unfold_machine_address_helpers
        simp [cache,metadata,get,getThe,MonadStateOf.get,EStateM.get,
          bind,EStateM.bind,pure,EStateM.pure,NonUBResult,
          throw,throwThe,MonadExceptOf.throw,EStateM.throw,NonUBResult,classifier,AddressErrorClass.address,AddressErrorClass.callback]
      | ok info =>
        let addrInfo : AllocationAddressInfo := {
          kind := if info.kind == .dead then .dead else if info.kind == .typeId then .typeId else .liveData
          live := state.memory.isAllocLive id
          size := info.size
          align := info.align
          memoryKind := some kind
          thread := UInt32.ofNat state.threads.activeThread.toNat }
        cases outcome : state.user.addresses.addrFromAllocId id (some addrInfo) choices ⟨none⟩ with
        | mk afterAddress result =>
          simp only [addrInfo,beq_iff_eq] at outcome
          cases result with
          | error error =>
            unfold MachineAddress.assign
            unfold_machine_address_helpers
            simp [cache,metadata,managed,noRace,outcome,
              get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
              modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,NonUBResult,
              throw,throwThe,MonadExceptOf.throw,EStateM.throw,NonUBResult,classifier,AddressErrorClass.address,AddressErrorClass.callback]
          | ok assignment =>
            cases assignment with
            | ready address =>
              unfold MachineAddress.assign
              unfold_machine_address_helpers
              simp [cache,metadata,managed,noRace,outcome,
                get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
                modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,NonUBResult,classifier,AddressErrorClass.address]
            | acquireRequired target address clock =>
              cases cached : afterAddress.cacheAddress target address with
              | mk cachedState result =>
                cases result <;>
                  unfold MachineAddress.assign <;>
                  unfold_machine_address_helpers <;>
                  simp [cache,metadata,managed,noRace,outcome,cached,
                    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
                    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,NonUBResult,
                    throw,throwThe,MonadExceptOf.throw,EStateM.throw,NonUBResult,classifier,AddressErrorClass.address,AddressErrorClass.callback]
/-- Managed assignment changes only the address state when no race engine is
installed, including the source effects retained on an error. -/
theorem shape {K U : Type} (h : Hooks K U) (state : State K U)
    (id : AllocId) (kind : Option AddressMemoryKind) (choices : AddressRandomChoices)
    (managed : state.user.addresses.addressMode = .managed)
    (noRace : state.dataRace = none) :
    ∃ addresses, MachineAddress.resultState (MachineAddress.assign h id kind choices state) =
      {state with user := {state.user with addresses}} := by
  cases cache : state.user.addresses.baseAddr.find? (fun row => row.allocId == id) with
  | some cached =>
    unfold MachineAddress.assign
    unfold_machine_address_helpers
    simp [cache,get,getThe,MonadStateOf.get,EStateM.get,
      bind,EStateM.bind,pure,EStateM.pure,MachineAddress.resultState] <;> exact ⟨_,rfl⟩
  | none =>
    cases kind with
    | none =>
      unfold MachineAddress.assign
      unfold_machine_address_helpers
      simp [cache,get,getThe,MonadStateOf.get,EStateM.get,
        bind,EStateM.bind,pure,EStateM.pure,MachineAddress.resultState,
        throw,throwThe,MonadExceptOf.throw,EStateM.throw,MachineAddress.resultState] <;> exact ⟨_,rfl⟩ <;> exact ⟨_,rfl⟩
    | some kind =>
      cases metadata : state.memory.getAllocInfo id with
      | error error =>
        unfold MachineAddress.assign
        unfold_machine_address_helpers
        simp [cache,metadata,get,getThe,MonadStateOf.get,EStateM.get,
          bind,EStateM.bind,pure,EStateM.pure,MachineAddress.resultState,
          throw,throwThe,MonadExceptOf.throw,EStateM.throw,MachineAddress.resultState] <;> exact ⟨_,rfl⟩ <;> exact ⟨_,rfl⟩
      | ok info =>
        let addrInfo : AllocationAddressInfo := {
          kind := if info.kind == .dead then .dead else if info.kind == .typeId then .typeId else .liveData
          live := state.memory.isAllocLive id
          size := info.size
          align := info.align
          memoryKind := some kind
          thread := UInt32.ofNat state.threads.activeThread.toNat }
        cases outcome : state.user.addresses.addrFromAllocId id (some addrInfo) choices ⟨none⟩ with
        | mk afterAddress result =>
          simp only [addrInfo,beq_iff_eq] at outcome
          cases result with
          | error error =>
            unfold MachineAddress.assign
            unfold_machine_address_helpers
            simp [cache,metadata,managed,noRace,outcome,
              get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
              modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,MachineAddress.resultState,
              throw,throwThe,MonadExceptOf.throw,EStateM.throw,MachineAddress.resultState] <;> exact ⟨_,rfl⟩ <;> exact ⟨_,rfl⟩
          | ok assignment =>
            cases assignment with
            | ready address =>
              unfold MachineAddress.assign
              unfold_machine_address_helpers
              simp [cache,metadata,managed,noRace,outcome,
                get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
                modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,MachineAddress.resultState] <;> exact ⟨_,rfl⟩
            | acquireRequired target address clock =>
              cases cached : afterAddress.cacheAddress target address with
              | mk cachedState result =>
                cases result <;>
                  unfold MachineAddress.assign <;>
                  unfold_machine_address_helpers <;>
                  simp [cache,metadata,managed,noRace,outcome,cached,
                    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
                    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,MachineAddress.resultState,
                    throw,throwThe,MonadExceptOf.throw,EStateM.throw,MachineAddress.resultState] <;> exact ⟨_,rfl⟩ <;> exact ⟨_,rfl⟩

end EmptyFunction.MachineAddressPartial
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.MachineAddressPartial.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved machine address partial axiom {dependency} in {name}"
