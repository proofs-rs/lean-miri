import empty_function.ProjectedAddress
import empty_function.AddressErrorClass
import empty_function.ChoicePartial
import empty_function.RelocationByteActual
namespace EmptyFunction.StackAddressPartial
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

private theorem cache_target (state : GlobalAddressState) (id : AllocId) (address : UInt64)
    (missing : state.baseAddr.find? (fun row => row.allocId == id) = none) :
    (state.cacheAddress id address).state.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,address⟩ := by
  unfold GlobalAddressState.cacheAddress
  unfold_source_base
  unfold_source_insert_base
  have noFilter : state.baseAddr.filter (fun row => row.allocId != id) = state.baseAddr := by
    apply Array.filter_eq_self.mpr
    intro row member
    have absent := Array.find?_eq_none.mp missing row member
    simp only [bne,absent,Bool.not_false]
  simp only [missing,Option.map_none,noFilter]
  repeat' first
    | (solve | simp only [Array.find?_push,missing,Option.or,Id.run,pure,beq_self_eq_true,↓reduceIte])
    | split

/-- A successful stack miss really generated its returned address. Neither
capacity nor positivity is assumed; unsuccessful checks stay explicit. -/
theorem raw_success (state : GlobalAddressState) (generation : AddressGenerationState)
    (id : AllocId) (info : AllocationAddressInfo) (slack : Fin 16)
    (managed : state.addressMode = .managed) (current : state.generation = some generation)
    (missing : state.baseAddr.find? (fun row => row.allocId == id) = none)
    (live : info.live = true) (data : info.kind = .liveData) (stack : info.memoryKind = some .stack)
    (assignment : AddressAssignment)
    (actual : (state.addrFromAllocId id (some info) ⟨false,false,0,slack⟩).outcome = .ok assignment) :
    ∃ base, assignment = .ready base ∧
      (generation.generator.generate info.size info.align slack).outcome = .ok base ∧
      (state.addrFromAllocId id (some info) ⟨false,false,0,slack⟩).state.baseAddr.find?
        (fun row => row.allocId == id) = some ⟨id,base⟩ := by
  revert actual
  unfold GlobalAddressState.addrFromAllocId
  unfold_source_base
  unfold_source_generation
  intro actual
  simp only [missing,Option.map_none,live,data,stack,managed,current,
    beq_self_eq_true,Bool.not_true,↓reduceIte,ReusePool.takeAddr,Id.run,pure,beq_iff_eq,
    reduceCtorEq,Bool.false_or,Bool.or_false] at actual ⊢
  cases generated : generation.generator.generate info.size info.align slack with
  | mk after outcome =>
    simp only [generated] at actual ⊢
    cases outcome with
    | error reason => simp at actual
    | ok base =>
      simp only at actual
      repeat' first | (solve | simp_all [cache_target]) | split at actual


/-- The actual framed stack assignment retains its real failure state, or
returns exactly the address update whose successful generator was checked. -/
theorem assign (hooks : ProjectedAddress.Hooks) (state : ProjectedAddress.State)
    (id : AllocId) (info : AllocationInfo) (generation : AddressGenerationState) (slack : Fin 16)
    (missing : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.machine.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData) (live : state.machine.memory.isAllocLive id = true)
    (managed : state.machine.user.addresses.addressMode = .managed)
    (current : state.machine.user.addresses.generation = some generation)
    (classifier : hooks.classifyAddressError = PointerSource.addressError) :
    (∃ base addresses,
      PointerMachine.addrFromAllocId hooks id (some .stack) ⟨false,false,0,slack⟩ state =
        .ok base (ProjectedAddress.assigned state addresses) ∧
      addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ ∧
      (generation.generator.generate info.size info.align slack).outcome = .ok base) ∨
    (∃ error failed,
      PointerMachine.addrFromAllocId hooks id (some .stack) ⟨false,false,0,slack⟩ state =
        .error error failed ∧ RunLoop.reportsUB error = false) := by
  let view : AllocationAddressInfo := ⟨.liveData,true,info.size,info.align,some .stack,
    UInt32.ofNat state.machine.threads.activeThread.toNat⟩
  cases actual : state.machine.user.addresses.addrFromAllocId id (some view) ⟨false,false,0,slack⟩ with
  | mk addresses outcome =>
    cases outcome with
    | error error =>
      refine .inr ⟨PointerSource.addressError error,ProjectedAddress.assigned state addresses,?_,AddressErrorClass.address error⟩
      unfold PointerMachine.addrFromAllocId
      unfold_pointer_address_helpers
      simp [missing,metadata,data,live,managed,view,ProjectedAddress.assigned,classifier,actual,
        get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
        modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
        throw,throwThe,MonadExceptOf.throw,EStateM.throw]
    | ok assignment =>
      have ready := raw_success state.machine.user.addresses generation id view slack managed current missing rfl rfl rfl
        assignment (by rw [actual])
      obtain ⟨base,equal,generated,cache⟩ := ready
      subst assignment
      refine .inl ⟨base,addresses,?_,?_,generated⟩
      · unfold PointerMachine.addrFromAllocId
        unfold_pointer_address_helpers
        simp [missing,metadata,data,live,managed,view,ProjectedAddress.assigned,actual,
          get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
          modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
      · simpa only [actual] using cache


/-- Actual stack address request for every tape and diagnostic policy. A
non-UB stop is distinct from the exact successful address/tape update. -/
theorem stack (hooks : ProjectedAddress.Hooks) (state : ProjectedAddress.State)
    (id : AllocId) (info : AllocationInfo) (generation : AddressGenerationState)
    (missing : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.machine.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData) (live : state.machine.memory.isAllocLive id = true)
    (managed : state.machine.user.addresses.addressMode = .managed)
    (current : state.machine.user.addresses.generation = some generation)
    (classifier : hooks.classifyAddressError = PointerSource.addressError) :
    (∃ base nextTape addresses, ∃ slack : Fin 16,
      ExecutionAddressChoices.addrFromAllocId ChoiceProjection.tapeAccess hooks id (some .stack) state =
        .ok base (ProjectedAddress.assigned (ChoiceProjection.tapeAccess.put state nextTape) addresses) ∧
      addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ ∧
      (generation.generator.generate info.size info.align slack).outcome = .ok base) ∨
    (∃ error failed,
      ExecutionAddressChoices.addrFromAllocId ChoiceProjection.tapeAccess hooks id (some .stack) state =
        .error error failed ∧ RunLoop.reportsUB error = false) := by
  have request := ChoiceProjection.stack_request hooks state id info generation missing metadata data live managed current
  have drawPost := ChoicePartial.index ChoiceProjection.tapeAccess state .addressSlack 16 (by intros; rfl)
  cases draw : ExecutionChoices.index ChoiceProjection.tapeAccess .addressSlack 16 state with
  | error error failed =>
    simp only [draw] at drawPost
    refine .inr ⟨error,failed,?_,drawPost⟩
    rw [request]
    simp only [bind,EStateM.bind,draw]
  | ok value drawn =>
    simp only [draw] at drawPost
    obtain ⟨supported,nextTape,equal⟩ := drawPost
    subst drawn
    have supplied : ExecutionAddressChoices.addrFromAllocId ChoiceProjection.tapeAccess hooks id (some .stack) state =
        PointerMachine.addrFromAllocId hooks id (some .stack) ⟨false,false,0,⟨value,supported⟩⟩
          (ChoiceProjection.tapeAccess.put state nextTape) := by
      rw [request]
      simp only [bind,EStateM.bind,draw,supported,↓reduceDIte]
    rcases assign hooks (ChoiceProjection.tapeAccess.put state nextTape) id info generation ⟨value,supported⟩
      missing metadata data live managed current classifier with successful | stopped
    · obtain ⟨base,addresses,actual,cache,generated⟩ := successful
      exact .inl ⟨base,nextTape,addresses,⟨value,supported⟩,supplied.trans actual,cache,generated⟩
    · obtain ⟨error,failed,actual,nonUB⟩ := stopped
      exact .inr ⟨error,failed,supplied.trans actual,nonUB⟩
end EmptyFunction.StackAddressPartial
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if ["EmptyFunction.StackAddressPartial.","EmptyFunction.ChoicePartial."].any (fun label =>
        (name.toString.splitOn label).length != 1) then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved partial stack address axiom {dependency} in {name}"
