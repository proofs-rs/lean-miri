import empty_function.RelocationEntry
import empty_function.RelocationInvariant
namespace EmptyFunction.RelocationMemoryStep
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open EmptyFunction.ChoiceSupply
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
/-- One ordinary-memory relocation with either an existing or newly generated
address. Remaining budgets, trees, cache/pool representation and the exact tape
suffix are derived from the actual result for every supplied legal response. -/
theorem step {budget : Nat} (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (hooks : ChoiceExecution.H)
    (externStatic : MIR.DefId → MachineAddress.M MiriMemoryKind ChoiceExecution.Payload (Pointer Provenance))
    (tracker : MachineHooks.BorrowState) (provenance : CtfeProvenance) (offset : UInt64)
    (source : Allocation CtfeProvenance Unit) (info : AllocationInfo)
    (remaining maximumSize maximumAlignment : Nat) (nextPlan : GlobalAddressState → Plan budget)
    (world : TreeRuntimeInput.World before.machine tracker)
    (numeric : InputDraft.GenerationResources generation remaining maximumSize maximumAlignment)
    (one : 1 ≤ remaining) (tagRoom : tracker.global.nextPointerTag.value.toNat+remaining < 2^64)
    (descriptor : before.machine.memory.findGlobal? provenance.allocId = some
      ⟨provenance.allocId,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (metadata : before.machine.memory.getAllocInfo provenance.allocId = .ok info)
    (notDead : info.kind ≠ .dead) (notType : info.kind ≠ .typeId)
    (live : before.machine.memory.isAllocLive provenance.allocId = true)
    (noRace : before.machine.dataRace = none)
    (alignment : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == provenance.allocId) = none →
      InputDraft.AlignmentRepresentation info.align)
    (sizeBound : info.size.bytes.toNat ≤ maximumSize)
    (alignBound : 2^info.align.pow2 ≤ maximumAlignment)
    (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩)
    (strict : (ChoiceExecution.tapeAccess.get before.machine).policy = .strict)
    (fitted : Fits (AddressChoicePlan.attempt before.machine.user.addresses provenance.allocId
      ⟨.liveData,true,info.size,info.align,some .other,UInt32.ofNat before.machine.threads.activeThread.toNat⟩ nextPlan)
      (ChoiceExecution.tapeAccess.get before.machine)) :
    ∃ pointer final next nextTracker,
      PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks externStatic
        (Pointer.new provenance (Size.ofBytes offset)) before.machine = .ok pointer final ∧
      final.memory = before.machine.memory ∧ final.threads = before.machine.threads ∧
      Fits (nextPlan final.user.addresses) (ChoiceExecution.tapeAccess.get final) ∧
      (ChoiceExecution.tapeAccess.get final).policy = .strict ∧
      InputDraft.GenerationRepresentation {before with machine := final} next ∧
      TreeRuntimeInput.World final nextTracker ∧
      nextTracker.global.nextPointerTag.value.toNat+(remaining-1) < 2^64 ∧
      InputDraft.GenerationResources next (remaining-1) maximumSize maximumAlignment ∧ final.dataRace = none ∧
      final.user.payload.payload.user.runtime = before.machine.user.payload.payload.user.runtime ∧
      RelocationContext.view final.user.payload = RelocationContext.view before.machine.user.payload ∧
      (∀ oldId old, before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == oldId) = some old →
        final.user.addresses.baseAddr.find? (fun row => row.allocId == oldId) = some old) ∧
      AddressStaticPost.view final.user.addresses = AddressStaticPost.view before.machine.user.addresses := by
  have tagOne : tracker.global.nextPointerTag.value.toNat+1 < 2^64 := by omega
  cases cached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == provenance.allocId) with
  | none =>
    have abi := alignment cached
    have valid := RawGenerator.normalized_exponent info.align abi.choose abi.choose_spec.2
    have alignNat : (RawGenerator.alignment info.align).toNat ≤ maximumAlignment := by
      rw [RawGenerator.alignment_nat info.align valid]
      exact alignBound
    have room : ∀ slack, RawGenerator.Room generation.generator info.size info.align slack := by
      intro slack
      exact RawGenerator.room_of_bounds generation.generator info.size info.align slack remaining maximumSize maximumAlignment
        one sizeBound alignNat numeric.arithmetic numeric.capacity
    obtain ⟨pointer,final,actual,memory,threads,tail,strictFinal,next,rep,shape,root,bases,staticPost⟩ := RelocationEntry.memory_fits
      before generation representation hooks externStatic tracker provenance offset source info nextPlan descriptor
      world.enabled tagOne cached metadata notDead notType live noRace abi room numeric.positiveCursor width strict fitted
    obtain ⟨nextTracker,worldPost,tags,resources⟩ := RelocationInvariant.successor before final tracker generation next
      remaining maximumSize maximumAlignment provenance.allocId info.size info.align world numeric one tagRoom valid
      sizeBound alignNat memory shape root
    obtain ⟨_,_,_,_,race,runtime,context⟩ := root
    exact ⟨pointer,final,next,nextTracker,actual,memory,threads,tail,strictFinal,rep,worldPost,tags,resources,race.trans noRace,runtime,context,bases,staticPost⟩
  | some row =>
    have identifier : row.allocId = provenance.allocId := by
      have test := Array.find?_some cached
      exact of_decide_eq_true test
    have cachedExact : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == provenance.allocId) =
        some ⟨provenance.allocId,row.address⟩ := by cases row; simp_all
    obtain ⟨tag,final,actual,memory,threads,addresses,tape,global,tagged,enabled,race,runtime,context⟩ :=
      RelocationRoot.memory_cached before.machine hooks externStatic tracker provenance offset row.address source descriptor
        world.enabled tagOne cachedExact width
    have tail : Fits (nextPlan final.user.addresses) (ChoiceExecution.tapeAccess.get final) := by
      simp only [AddressChoicePlan.attempt,cached,Option.isSome_some,↓reduceIte,fits_pad] at fitted
      simpa only [addresses,tape] using fitted
    have rep := AddressTransport.representation before {before with machine := final} memory addresses generation representation
    have worldPost := RootTagPost.world before.machine final tracker global provenance.allocId tag world memory enabled tagged
    have rootPost := RootTagPost.root tracker.global provenance.allocId global tag tagged
    have tags := RelocationNumeric.tag_remaining _ _ remaining one tagRoom rootPost.2.2.2.2.2.1
    have resources := RelocationNumeric.unchanged generation generation.reusePool remaining maximumSize maximumAlignment numeric
    have strictFinal : (ChoiceExecution.tapeAccess.get final).policy = .strict := by rw [tape]; exact strict
    exact ⟨_,final,generation,{tracker with global},actual,memory,threads,tail,strictFinal,rep,worldPost,tags,resources,race.trans noRace,runtime,context,(by intro oldId old prior; rw [addresses]; exact prior),(by rw [addresses])⟩
end EmptyFunction.RelocationMemoryStep
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RelocationMemoryStep.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved relocation memory step axiom {dependency} in {name}"
