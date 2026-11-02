import empty_function.RelocationAddress
namespace EmptyFunction.RelocationPost
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def withAddresses (state : ChoiceExecution.S) (addresses : GlobalAddressState) : ChoiceExecution.S :=
  {state with user := {state.user with addresses}}

/-- A postcondition of the real successful assign, not an input validity law.
It identifies the actual address maps with the exact source-plan successor,
including the real no-race acquireRequired/cache branch. -/
theorem assignment_state (hooks : ChoiceExecution.H) (state : ChoiceExecution.S)
    (id : AllocId) (info : AllocationInfo) (choices : AddressRandomChoices)
    (missing : state.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.memory.getAllocInfo id = .ok info)
    (notDead : info.kind ≠ .dead) (notType : info.kind ≠ .typeId)
    (live : state.memory.isAllocLive id = true)
    (managed : state.user.addresses.addressMode = .managed) (noRace : state.dataRace = none)
    (value : UInt64) (after : ChoiceExecution.S)
    (actual : MachineAddress.assign hooks id (some .other) choices state = .ok value after) :
    AddressChoicePlan.assignedState (state.user.addresses.addrFromAllocId id
      (some ⟨.liveData,true,info.size,info.align,some .other,UInt32.ofNat state.threads.activeThread.toNat⟩) choices) =
      .ok after.user.addresses := by
  let addrInfo : AllocationAddressInfo :=
    ⟨.liveData,true,info.size,info.align,some .other,UInt32.ofNat state.threads.activeThread.toNat⟩
  cases outcome : state.user.addresses.addrFromAllocId id (some addrInfo) choices ⟨none⟩ with
  | mk addresses result =>
    simp only [addrInfo] at outcome
    cases result with
    | error error =>
      have run : MachineAddress.assign hooks id (some .other) choices state =
          .error (hooks.classifyAddressError error) (withAddresses state addresses) := by
        unfold MachineAddress.assign
        unfold_machine_address_helpers
        simp [missing,metadata,notDead,notType,live,managed,noRace,outcome,withAddresses,
          get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
          modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
          throw,throwThe,MonadExceptOf.throw,EStateM.throw]
      rw [run] at actual
      cases actual
    | ok assignment =>
      cases assignment with
      | ready base =>
        have run : MachineAddress.assign hooks id (some .other) choices state =
            .ok base (withAddresses state addresses) := by
          unfold MachineAddress.assign
          unfold_machine_address_helpers
          simp [missing,metadata,notDead,notType,live,managed,noRace,outcome,withAddresses,
            get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
            modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
        rw [run] at actual
        cases actual
        simp only [AddressChoicePlan.assignedState,withAddresses]
      | acquireRequired target base clock =>
        cases cached : addresses.cacheAddress target base with
        | mk cachedState result =>
          cases result with
          | error error =>
            have run : MachineAddress.assign hooks id (some .other) choices state =
                .error (hooks.classifyAddressError error) (withAddresses state cachedState) := by
              unfold MachineAddress.assign
              unfold_machine_address_helpers
              simp [missing,metadata,notDead,notType,live,managed,noRace,outcome,cached,withAddresses,
                get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
                modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
                throw,throwThe,MonadExceptOf.throw,EStateM.throw]
            rw [run] at actual
            cases actual
          | ok done =>
            cases done
            have run : MachineAddress.assign hooks id (some .other) choices state =
                .ok base (withAddresses state cachedState) := by
              unfold MachineAddress.assign
              unfold_machine_address_helpers
              simp [missing,metadata,notDead,notType,live,managed,noRace,outcome,cached,withAddresses,
                get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
                modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
            rw [run] at actual
            cases actual
            simp only [AddressChoicePlan.assignedState,cached,withAddresses]
end EmptyFunction.RelocationPost
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RelocationPost.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved relocation post axiom {dependency} in {name}"
