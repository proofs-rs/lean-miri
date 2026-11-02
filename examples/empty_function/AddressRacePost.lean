import empty_function.ChoiceExecution
namespace Miri.Interpreter.MachineAddress
open Miri Miri.Memory Miri.Memory.AllocAddresses
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
variable {K U : Type}
theorem assign_no_race (h : Hooks K U) (state : State K U)
    (id : AllocId) (kind : Option AddressMemoryKind) (choices : AddressRandomChoices)
    (managed : state.user.addresses.addressMode = .managed)
    (noRace : state.dataRace = none) :
    (resultState (assign h id kind choices state)).dataRace = state.dataRace := by
  unfold assign
  unfold_machine_address_helpers
  cases cache : state.user.addresses.baseAddr.find? (fun row => row.allocId == id) with
  | some cached =>
    simp [noRace,cache,get,getThe,MonadStateOf.get,EStateM.get,
      bind,EStateM.bind,pure,EStateM.pure,resultState]
  | none =>
    cases kind with
    | none =>
      simp [noRace,cache,get,getThe,MonadStateOf.get,EStateM.get,
        bind,EStateM.bind,pure,EStateM.pure,resultState,
        throw,throwThe,MonadExceptOf.throw,EStateM.throw]
    | some kind =>
      cases metadata : state.memory.getAllocInfo id with
      | error error =>
        simp [noRace,cache,metadata,get,getThe,MonadStateOf.get,EStateM.get,
          bind,EStateM.bind,pure,EStateM.pure,resultState,
          throw,throwThe,MonadExceptOf.throw,EStateM.throw]
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
            simp [cache,metadata,managed,noRace,outcome,
              get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
              modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,resultState,
              throw,throwThe,MonadExceptOf.throw,EStateM.throw]
          | ok assignment =>
            cases assignment with
            | ready address =>
              simp [cache,metadata,managed,noRace,outcome,
                get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
                modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,resultState]
            | acquireRequired target address clock =>
              cases cached : afterAddress.cacheAddress target address with
              | mk cachedState result =>
                cases result <;>
                  simp [cache,metadata,managed,noRace,outcome,cached,
                    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
                    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,resultState,
                    throw,throwThe,MonadExceptOf.throw,EStateM.throw]

end Miri.Interpreter.MachineAddress
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``Miri.Interpreter.MachineAddress.assign_no_race) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved race post axiom {dependency}"
