import empty_function.ReuseNonePost
import empty_function.GeneratedShortagePost
namespace EmptyFunction.AddressAssignedSuccessPost
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open EmptyFunction.AddressPost
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem backing_withAddresses (before : WholeCall.State) (addresses : GlobalAddressState)
    (id : AllocId) (backing : InputDraft.MetadataBacking before id) :
    InputDraft.MetadataBacking (withAddresses before addresses) id := by
  cases backing with
  | live entry row => exact .live entry row
  | global entry row identity => exact .global entry row identity
  | extraFunction row => exact .extraFunction row
  | vaList row => exact .vaList row
  | dead entry row => exact .dead entry row

/-- Invert the actual pure assignment, preserving every current geometry
field on success. No capacity/probability/cursor margin is required. -/
theorem assigned (before : WholeCall.State) (generation : AddressGenerationState)
    (current : InputDraft.GenerationRepresentation before generation)
    (id : AllocId) (target : AllocationInfo) (thread : AddressThreadId)
    (choices : AddressRandomChoices) (after : GlobalAddressState)
    (backing : InputDraft.MetadataBacking before id)
    (live : before.machine.memory.isAllocLive id = true)
    (metadata : before.machine.memory.getAllocInfo id = .ok target)
    (alignment : (before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id)) = none →
      target.kind ≠ .typeId → InputDraft.AlignmentRepresentation target.align)
    (actual : AddressChoicePlan.assignedState (before.machine.user.addresses.addrFromAllocId id
      (some ⟨if target.kind == .typeId then .typeId else .liveData,true,target.size,target.align,some .other,thread⟩)
      choices) = .ok after) :
    ∃ next, InputDraft.GenerationRepresentation (withAddresses before after) next := by
  rcases choices with ⟨reuse,cross,selection,slack⟩
  have original := actual
  cases cached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) with
  | some row =>
    revert actual
    unfold GlobalAddressState.addrFromAllocId
    unfold_source_base
    intro actual
    simp only [cached,Option.map_some,AddressChoicePlan.assignedState,Id.run,pure] at actual
    cases actual
    exact ⟨generation,by simpa only [withAddresses] using current⟩
  | none =>
    by_cases typeId : target.kind = .typeId
    · have cachedZero := AddressPost.cache_zero before.machine.user.addresses id cached
      revert actual
      unfold GlobalAddressState.addrFromAllocId
      unfold_source_base
      intro actual
      simp [cached,typeId,cachedZero,AddressChoicePlan.assignedState,Id.run,pure,Pure.pure] at actual
      cases actual
      exact ⟨generation,by simpa only [cachedZero] using AddressPost.cache_zero_representation before generation current id cached⟩
    · have supportedAlignment := alignment cached typeId
      obtain ⟨bytes,bytesEq,normalized⟩ := supportedAlignment
      have normalizedActual : AddressChoicePlan.assignedState (before.machine.user.addresses.addrFromAllocId id
          (some ⟨.liveData,true,target.size,target.align,some .other,thread⟩) ⟨reuse,cross,selection,slack⟩) = .ok after := by
        simpa only [typeId,beq_iff_eq,↓reduceIte] using original
      revert actual
      unfold GlobalAddressState.addrFromAllocId
      unfold_source_base
      unfold_source_generation
      intro actual
      simp only [cached,Option.map_none,typeId,beq_iff_eq,↓reduceIte,
        current.managed,current.current,Id.run,pure] at actual
      cases taken : generation.reusePool.takeAddr reuse cross selection target.size target.align .other thread with
      | mk pool result =>
        cases result with
        | error error =>
          simp only [taken,AddressChoicePlan.assignedState] at actual
          cases actual
        | ok used =>
          cases used with
          | some used =>
            have takeOutcome := congrArg (fun (result : ReusePoolResult (Option ReusedAddress)) => result.outcome) taken
            have isReuse : reuse = true := by
              cases reuse with
              | true => rfl
              | false =>
                by_cases allowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseRate false = true
                · simp [ReusePool.takeAddr,allowed,Id.run,pure,Pure.pure] at takeOutcome
                · have denied : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseRate false = false := by simpa using allowed
                  simp [ReusePool.takeAddr,denied,Id.run,pure,Pure.pure] at takeOutcome
            subst reuse
            obtain ⟨bucket,present⟩ := ReuseSuccessBucket.present generation.reusePool target.size target.align bytes thread cross selection used
              bytesEq normalized takeOutcome
            exact ReuseSuccessPost.representation before generation current id target thread bucket cross selection slack used after
              cached backing live metadata present ⟨bytes,bytesEq,normalized⟩ takeOutcome normalizedActual
          | none =>
            let nextGen := {generation with reusePool := pool}
            let beforeTake := withAddresses before {before.machine.user.addresses with generation := some nextGen}
            have takenRep : InputDraft.GenerationRepresentation beforeTake nextGen :=
              ReuseNonePost.representation before generation current pool target.size target.align bytes thread reuse cross selection bytesEq normalized taken
            cases generated : generation.generator.generate target.size target.align slack with
            | mk generator outcome =>
              cases outcome with
              | error error =>
                simp only [taken,generated,AddressChoicePlan.assignedState] at actual
                cases actual
              | ok base =>
                have post := GeneratedShortagePost.cache beforeTake nextGen takenRep id target slack generator base generated
                  cached (backing_withAddresses before _ id backing) live metadata
                simp only [show (AllocationAddressKind.liveData == AllocationAddressKind.dead) = false from rfl,
                  Bool.not_true,Bool.false_or,Bool.false_eq_true,reduceCtorEq,↓reduceIte,taken,generated] at actual
                simp only [←current.managed] at actual
                let ready := {before.machine.user.addresses with generation := some (GeneratedShortagePost.next nextGen generator)}
                change AddressChoicePlan.assignedState
                  (match (ready.cacheAddress id base).outcome with
                  | .ok _ => ⟨(ready.cacheAddress id base).state,.ok (.ready base)⟩
                  | .error error => ⟨(ready.cacheAddress id base).state,.error error⟩) = .ok after at actual
                change InputDraft.GenerationRepresentation
                  (withAddresses before (ready.cacheAddress id base).state)
                  (GeneratedShortagePost.next nextGen generator) at post
                cases cachedResult : ready.cacheAddress id base with
                | mk cachedState outcome =>
                  cases outcome with
                  | error error =>
                    simp only [cachedResult,AddressChoicePlan.assignedState] at actual
                    cases actual
                  | ok _done =>
                    simp only [cachedResult,AddressChoicePlan.assignedState] at actual
                    cases actual
                    exact ⟨_,by simpa only [cachedResult] using post⟩
end EmptyFunction.AddressAssignedSuccessPost

open Lean in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.AddressAssignedSuccessPost.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved assigned-success axiom {dependency} in {name}"
