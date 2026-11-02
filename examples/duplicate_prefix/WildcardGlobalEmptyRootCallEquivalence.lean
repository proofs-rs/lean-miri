import duplicate_prefix.WildcardGlobalEmptyRootArgumentScope
import duplicate_prefix.GlobalEmptyRootPrepared
import duplicate_prefix.WildcardPoolHitRootArgumentScope
import duplicate_prefix.RawRootInvocation

namespace DuplicatePrefix.WildcardGlobalEmptyRootCallEquivalence
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts RootFrameData EmptyRootArguments ActualReferenceContext ConcreteEmptyRootArguments ConcreteEmptyRootArgumentScope
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

theorem call_eq
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (actualPointers : ctx.pointers = GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler
      PreparedReflection.actual.image (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ())
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (tracker : MachineHooks.BorrowState)
    (base offset n : UInt64) (nonzero : base+offset ≠ 0)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (enabled : before.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (distinct : parentTag ≠ tracker.global.nextPointerTag)
    (source : Allocation CtfeProvenance Unit) (supported : GlobalSupportedImage.Supported source PreparedReflection.actual.compiler.runtime.target
      before.memory tracker.global.rootPointerTags before.user.addresses.baseAddr)
    (rootCached : tracker.global.rootTag? id = some parentTag) (race : before.dataRace = none)
    (noExtras : (before.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id)) = false)
    (absent : before.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : before.memory.hasFunctionPointer id = false) (noVaList : before.memory.hasVaListId id = false)
    (descriptor : before.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (addressMode : before.user.addresses.provenanceMode ≠ .strict)
    (geometry : WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap (base+offset) base id source.byteSize)
    (exposed : before.user.addresses.exposed.contains id = true)
    (allocLive : before.memory.isAllocLive id = true)
    (metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (place : MPlaceTy Provenance) (thread : Miri.Concurrency.ThreadRecord)
    (active : before.threads.activeThread? = some thread) (noCache : thread.topUserRelevantFrame = none) :
    ∃ converted : Allocation Provenance Unit, GlobalAllocationAttributes.Attributes source converted ∧
      let h := ExecutionMachine.callHooks (config options (remaining+1) span) limits
      let first : OpTy Provenance := ⟨.immediate (RetagReferencePlace.sliceValue
        (config options remaining span).access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm,
        ActualReferenceMetadata.reference⟩
      Call.initStackFrame h () RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy first,.Copy (second n)] false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ =
      Call.initStackFrame h () RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy first,.Copy (second n)] false (.memory place) (.stop true)
          ⟨⟨#[]⟩,WildcardGlobalEmptyRootCopy.preparedMachine options before id parentTag source converted⟩ := by
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
  have enabledRaw : machine.borrowTracker = some tracker := borrow.trans enabled
  have cachedRaw : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by rw [addresses];exact cachedAddress
  have absentRaw : machine.memory.live.find? (fun row => row.1 == id) = none := by rw [memory];exact absent
  have noFunctionRaw : machine.memory.hasFunctionPointer id = false := by rw [memory];exact noFunction
  have noVaListRaw : machine.memory.hasVaListId id = false := by rw [memory];exact noVaList
  have descriptorRaw : machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩ := by rw [memory];exact descriptor
  have noExtrasRaw : (machine.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id)) = false := by
    rw [extraEq];exact noExtras
  have supportedRaw : GlobalSupportedImage.Supported source PreparedReflection.actual.compiler.runtime.target
      machine.memory tracker.global.rootPointerTags machine.user.addresses.baseAddr := by
    rw [memory,addresses];exact supported
  have raceRaw : machine.dataRace = none := dataRace.trans race
  have ghostRaw : machine.user.payload.ghost = false := ghostEq.trans ghost
  have shallowRaw : machine.user.payload.validation = .Shallow := validation.trans shallow
  have metadataRaw : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime := by rw [types];exact metadata
  have notConstructedRaw : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false := by rw [types];exact notConstructed
  have modeRaw : machine.user.addresses.provenanceMode ≠ .strict := by rw [addresses];exact addressMode
  have geometryRaw : WildcardGeneralHitReborrow.Geometry machine.user.addresses.intToPtrMap (base+offset) base id source.byteSize := by rw [addresses];exact geometry
  have exposedRaw : machine.user.addresses.exposed.contains id = true := by rw [addresses];exact exposed
  have allocLiveRaw : machine.memory.isAllocLive id = true := by rw [memory];exact allocLive
  obtain ⟨converted,facts,arguments⟩ := WildcardGlobalEmptyRootArgumentScope.scope options limits remaining span ctx actualPointers
    debugOff cmp dynamicFuel validityFuel fuelEq validationEq id parentTag tracker base offset n nonzero
    #[] raw machine (congrArg (fun row => row.value) (slot i1)) (congrArg (fun row => row.layout) (slot i1))
    (congrArg (fun row => row.value) (slot i2)) (congrArg (fun row => row.layout) (slot i2)) ghostRaw shallowRaw
    cachedRaw {} frameBorrow enabledRaw fresh distinct source supportedRaw rootCached raceRaw noExtrasRaw absentRaw
    noFunctionRaw noVaListRaw descriptorRaw modeRaw geometryRaw exposedRaw allocLiveRaw metadataRaw notConstructedRaw
  refine ⟨converted,facts,?_⟩
  let prepared := WildcardGlobalEmptyRootCopy.preparedMachine options machine id parentTag source converted
  let entry := WildcardGlobalEmptyRootCopy.entry parentTag source converted
  have present : prepared.memory.live.find? (fun row => row.1 == id) = some (id,entry) :=
    MemoryCopyBridge.live_lookup_replaced machine.memory id entry
  have size : entry.allocation.byteSize = Size.ofBytes source.byteSize.bytes := facts.size
  have geometryPrepared : WildcardGeneralHitReborrow.Geometry prepared.user.addresses.intToPtrMap
      (base+offset) base id entry.allocation.byteSize := by
    change WildcardGeneralHitReborrow.Geometry machine.user.addresses.intToPtrMap (base+offset) base id converted.byteSize
    rw [facts.size]
    exact geometryRaw
  have tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tracker.global.nextPointerTag := by
    intro row member
    change row ∈ (#[(parentTag,(⟨0⟩ : UniIndex))] : Array (BorTag × UniIndex)) at member
    have equal : row = (parentTag,(⟨0⟩ : UniIndex)) := by simpa only [Array.mem_singleton] using member
    rw [equal]
    exact distinct
  let rootSlot := WildcardGlobalEmptyReferenceReborrow.rootSlot parentTag source.byteSize
  have oldArguments := WildcardPoolHitRootArgumentScope.scope options limits remaining span ctx debugOff cmp dynamicFuel
    validityFuel fuelEq validationEq id tracker base offset n nonzero entry #[] raw prepared
    (congrArg (fun row => row.value) (slot i1)) (congrArg (fun row => row.layout) (slot i1))
    (congrArg (fun row => row.value) (slot i2)) (congrArg (fun row => row.layout) (slot i2)) ghostRaw shallowRaw
    cachedRaw present {} frameBorrow enabledRaw fresh modeRaw geometryPrepared exposedRaw tagFresh rootSlot metadataRaw notConstructedRaw

  let original : RootState := ⟨⟨#[]⟩,before⟩
  let preparedOriginal : RootState := ⟨⟨#[]⟩,WildcardGlobalEmptyRootCopy.preparedMachine options before id parentTag source converted⟩
  have push := CallEntryFacts.actual_call_hooks_push_raw options () (remaining+1) span limits debugOff original (.memory place) thread active noCache
  have pushPrepared := CallEntryFacts.actual_call_hooks_push_raw options () (remaining+1) span limits debugOff
    preparedOriginal (.memory place) thread active noCache
  have rawPrepared : CallEntryFacts.rawPushedState #[] preparedOriginal.machine (.memory place) =
      Storage.withCurrent #[] raw.frame prepared := by rfl
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span #[] raw.frame machine
  have getPrepared := CallEntryLocals.get_frame options limits (remaining+1) span #[] raw.frame prepared
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span #[] raw.frame raw.frame machine
  have setPrepared := CallEntryLocals.set_frame options limits (remaining+1) span #[] raw.frame raw.frame prepared
  have control := RawRootInvocation.control before place race
  have preamble : raw.frame.location = .unwinding ⟨559⟩ := control.1
  have unchanged : {raw.frame with trackCallerArg := none} = raw.frame := by rw [←control.2.1]
  dsimp only
  rw [RootCallCore.actual_entry_eq]
  unfold RootCallCore.core
  simp only [bind,Bind.bind,EStateM.bind]
  unfold CallEntryFacts.config at push pushPrepared
  rw [push,pushPrepared,RawRootInvocation.raw_eq #[] before place race,rawPrepared]
  simp only [EStateM.bind]
  rw [getFrame,getPrepared]
  simp only [EStateM.bind,preamble,pure,Pure.pure,EStateM.pure]
  simp only [preamble] at unchanged
  rw [unchanged,setFrame,setPrepared]
  simp only [EStateM.bind]
  rw [arguments,oldArguments]
  rfl

end
end DuplicatePrefix.WildcardGlobalEmptyRootCallEquivalence
