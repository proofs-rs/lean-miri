import duplicate_prefix.S03WildcardNonliveScope
import duplicate_prefix.RawRootInvocation
namespace DuplicatePrefix.S03WildcardNonliveCallEquality
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts RootFrameData EmptyRootArguments ActualReferenceContext ConcreteEmptyRootArguments
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Exact original initialization, not a successful-call premise: the exposed
wildcard exact-base or interior nondata hit normalizes to the same argument state as a concrete pointer.
All later errors/returns are therefore the SAME computation. -/
theorem call_equal
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (tracker : MachineHooks.BorrowState)
    (base offset n : UInt64) (nonzero : base+offset ≠ 0)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (info : AllocationInfo) (allocationInfo : before.memory.getAllocInfo id = .ok info)
    (nonlive : info.kind ≠ .liveData)
    (geometry : WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap (base+offset) base id info.size)
    (nonstrict : before.user.addresses.provenanceMode ≠ .strict)
    (exposed : before.user.addresses.exposed.contains id = true)
    (allocLive : before.memory.isAllocLive id = true)
    (enabled : before.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (race : before.dataRace = none)
    (metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (place : MPlaceTy Provenance)
    (thread : Miri.Concurrency.ThreadRecord)
    (active : before.threads.activeThread? = some thread)
    (noCache : thread.topUserRelevantFrame = none) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let first (p : Provenance) := (RetagReferencePlace.sliceValue
      (ActualReferenceContext.config options remaining span).access.runtime.base (Pointer.new p (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference)
    Call.initStackFrame (ExecutionMachine.callHooks cfg limits) () RootBody.reflected.functionInstance
      RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy ⟨.immediate (first .wildcard).imm,ActualReferenceMetadata.reference⟩,.Copy (second n)] false (.memory place) (.stop true)
      ⟨⟨#[]⟩,before⟩ =
    Call.initStackFrame (ExecutionMachine.callHooks cfg limits) () RootBody.reflected.functionInstance
      RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy ⟨.immediate (first (.concrete id parentTag)).imm,ActualReferenceMetadata.reference⟩,.Copy (second n)] false (.memory place) (.stop true)
      ⟨⟨#[]⟩,before⟩ := by
  dsimp only
  let raw := RawRootInvocation.root before place race
  let machine := RawRootInvocation.machine #[] before
  obtain ⟨memory,borrow,dataRace,addresses,ghostEq,validation,types,backend,extraEq⟩ := RawRootInvocation.preservation #[] before
  have slot (i : Fin 25) : (raw.frame.locals[i.val]'(raw.valid i)) = ⟨.dead,none⟩ := by
    have rows := congrArg (fun rows : Array (LocalState Provenance LocalLayout) => rows[i.val]?)
      (RawRootInvocation.locals before place race)
    have row : raw.frame.locals[i.val]?=some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
      simpa only [Array.getElem?_replicate,i.isLt,↓reduceIte] using rows
    exact Option.some.inj ((Array.getElem?_eq_getElem (raw.valid i)).symm.trans row)
  have frameBorrow := RawRootInvocation.frame_borrow before place race tracker enabled
  have control := RawRootInvocation.control before place race
  have cachedRaw : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by rw [addresses];exact cachedAddress
  have infoRaw : machine.memory.getAllocInfo id = .ok info := by rw [memory];exact allocationInfo
  have enabledRaw : machine.borrowTracker = some tracker := borrow.trans enabled
  have metadataRaw : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime := by rw [types];exact metadata
  have notConstructedRaw : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false := by rw [types];exact notConstructed
  have wild := S03WildcardNonliveScope.scope options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id tracker base offset n nonzero #[] raw machine
    (congrArg (fun row => row.value) (slot i1)) (congrArg (fun row => row.layout) (slot i1))
    (congrArg (fun row => row.value) (slot i2)) (congrArg (fun row => row.layout) (slot i2))
    (ghostEq.trans ghost) (validation.trans shallow) cachedRaw info infoRaw nonlive
    (by rw [addresses];exact geometry)
    (by rw [addresses];exact nonstrict) (by rw [addresses];exact exposed) (by rw [memory];exact allocLive)
    {} frameBorrow enabledRaw fresh metadataRaw notConstructedRaw
  have concrete := NonliveEmptyRootArgumentScope.scope options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id parentTag tracker base offset n nonzero #[] raw machine
    (congrArg (fun row => row.value) (slot i1)) (congrArg (fun row => row.layout) (slot i1))
    (congrArg (fun row => row.value) (slot i2)) (congrArg (fun row => row.layout) (slot i2))
    (ghostEq.trans ghost) (validation.trans shallow) cachedRaw info infoRaw nonlive {} frameBorrow enabledRaw fresh metadataRaw notConstructedRaw
  have arguments := wild.trans concrete.symm
  have push := CallEntryFacts.actual_call_hooks_push_raw options () (remaining+1) span limits debugOff
    (⟨⟨#[]⟩,before⟩ : RootState) (.memory place) thread active noCache
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span #[] raw.frame machine
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span #[] raw.frame raw.frame machine
  have unchanged : {raw.frame with trackCallerArg := none, location := .unwinding ⟨559⟩} = raw.frame := by rw [←control.1,←control.2.1]
  rw [RootCallCore.actual_entry_eq,RootCallCore.actual_entry_eq]
  unfold RootCallCore.core
  unfold CallEntryFacts.config at push
  simp only [bind,EStateM.bind]
  rw [push,RawRootInvocation.raw_eq #[] before place race]
  simp only [EStateM.bind]
  rw [getFrame]
  simp only [EStateM.bind]
  rw [show raw.frame.location = .unwinding ⟨559⟩ from control.1]
  simp only [pure,EStateM.pure,EStateM.bind]
  rw [unchanged,setFrame]
  simp only [EStateM.bind]
  rw [arguments]
end
end DuplicatePrefix.S03WildcardNonliveCallEquality
