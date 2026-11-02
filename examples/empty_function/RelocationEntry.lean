import empty_function.RelocationRoot
import empty_function.AddressTransport
import empty_function.AddressGenerationPost
import empty_function.AddressBasePost
import empty_function.AddressStaticPost
namespace EmptyFunction.RelocationEntry
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open EmptyFunction.ChoiceSupply
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem final_representation (before : WholeCall.State) (generation : AddressGenerationState)
    (id : AllocId) (info : AllocationAddressInfo) (choices : AddressRandomChoices)
    (current : before.machine.user.addresses.generation = some generation)
    (managed : before.machine.user.addresses.addressMode = .managed)
    (final : ChoiceExecution.S) (tracker : MachineHooks.BorrowState)
    (taggedPost : ∃ global tag, tracker.global.rootPointerTag id = .ok (global,tag) ∧
      final.borrowTracker = some {tracker with global} ∧ final.dataRace = before.machine.dataRace ∧
      final.user.payload.payload.user.runtime = before.machine.user.payload.payload.user.runtime ∧
      RelocationContext.view final.user.payload = RelocationContext.view before.machine.user.payload)
    (memory : final.memory = before.machine.memory)
    (successor : AddressChoicePlan.assignedState
      (before.machine.user.addresses.addrFromAllocId id (some info) choices) = .ok final.user.addresses)
    (post : ∃ after next, AddressChoicePlan.assignedState
      (before.machine.user.addresses.addrFromAllocId id (some info) choices) = .ok after ∧
      InputDraft.GenerationRepresentation (AddressPost.withAddresses before after) next) :
    ∃ next, InputDraft.GenerationRepresentation {before with machine := final} next ∧
      (next.generator = generation.generator ∨ ∃ slack : Fin 16,
        next.generator = (generation.generator.generate info.size info.align slack).state) ∧
      (∃ global tag, tracker.global.rootPointerTag id = .ok (global,tag) ∧
        final.borrowTracker = some {tracker with global} ∧ final.dataRace = before.machine.dataRace ∧
      final.user.payload.payload.user.runtime = before.machine.user.payload.payload.user.runtime ∧
      RelocationContext.view final.user.payload = RelocationContext.view before.machine.user.payload) ∧
      (∀ oldId old, before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == oldId) = some old →
        final.user.addresses.baseAddr.find? (fun row => row.allocId == oldId) = some old) ∧
      AddressStaticPost.view final.user.addresses = AddressStaticPost.view before.machine.user.addresses := by
  obtain ⟨after,next,actual,representation⟩ := post
  have same : after = final.user.addresses := Except.ok.inj (actual.symm.trans successor)
  subst after
  obtain ⟨numeric,nextCurrent,shape⟩ := AddressGenerationPost.generator_shape before.machine.user.addresses
    generation id info choices current managed final.user.addresses successor
  have nextEq : numeric = next := Option.some.inj (nextCurrent.symm.trans representation.current)
  subst numeric
  refine ⟨next,AddressTransport.representation (AddressPost.withAddresses before final.user.addresses)
    {before with machine := final} memory rfl next representation,?_,taggedPost,AddressBasePost.retained _ id info choices _ successor,AddressStaticPost.assignment _ id info choices _ successor⟩
  rcases shape with unchanged | generated
  · exact Or.inl unchanged
  · exact Or.inr ⟨choices.slack,generated⟩

/-- Fixed raw root descriptor and actual source-derived demand grammar. This
is one ordinary compiler-memory target branch, retaining all permitted choices. -/
theorem memory_fits {budget : Nat} (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (hooks : ChoiceExecution.H)
    (externStatic : Miri.MIR.DefId → MachineAddress.M MiriMemoryKind ChoiceExecution.Payload (Pointer Provenance))
    (tracker : MachineHooks.BorrowState) (provenance : CtfeProvenance) (offset : UInt64)
    (source : Allocation CtfeProvenance Unit) (info : AllocationInfo)
    (nextPlan : GlobalAddressState → Plan budget)
    (descriptor : before.machine.memory.findGlobal? provenance.allocId = some
      ⟨provenance.allocId,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (enabled : before.machine.borrowTracker = some tracker)
    (tagRoom : tracker.global.nextPointerTag.value.toNat + 1 < 2^64)
    (missing : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == provenance.allocId) = none)
    (metadata : before.machine.memory.getAllocInfo provenance.allocId = .ok info)
    (notDead : info.kind ≠ .dead) (notType : info.kind ≠ .typeId)
    (live : before.machine.memory.isAllocLive provenance.allocId = true)
    (noRace : before.machine.dataRace = none)
    (alignment : InputDraft.AlignmentRepresentation info.align)
    (room : ∀ slack, RawGenerator.Room generation.generator info.size info.align slack)
    (positive : 0 < generation.generator.nextBaseAddr.toNat)
    (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩)
    (strict : (ChoiceExecution.tapeAccess.get before.machine).policy = .strict)
    (fitted : Fits (AddressChoicePlan.attempt before.machine.user.addresses provenance.allocId
      ⟨.liveData,true,info.size,info.align,some .other,UInt32.ofNat before.machine.threads.activeThread.toNat⟩ nextPlan)
      (ChoiceExecution.tapeAccess.get before.machine)) :
    ∃ pointer final, PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks externStatic
      (Pointer.new provenance (Size.ofBytes offset)) before.machine = .ok pointer final ∧
      final.memory = before.machine.memory ∧ final.threads = before.machine.threads ∧
      Fits (nextPlan final.user.addresses) (ChoiceExecution.tapeAccess.get final) ∧
      (ChoiceExecution.tapeAccess.get final).policy = .strict ∧
      ∃ nextGen, InputDraft.GenerationRepresentation {before with machine := final} nextGen ∧
        (nextGen.generator = generation.generator ∨ ∃ slack : Fin 16,
          nextGen.generator = (generation.generator.generate info.size info.align slack).state) ∧
        (∃ global tag, tracker.global.rootPointerTag provenance.allocId = .ok (global,tag) ∧
          final.borrowTracker = some {tracker with global} ∧ final.dataRace = before.machine.dataRace ∧
      final.user.payload.payload.user.runtime = before.machine.user.payload.payload.user.runtime ∧
      RelocationContext.view final.user.payload = RelocationContext.view before.machine.user.payload) ∧
      (∀ oldId old, before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == oldId) = some old →
        final.user.addresses.baseAddr.find? (fun row => row.allocId == oldId) = some old) ∧
      AddressStaticPost.view final.user.addresses = AddressStaticPost.view before.machine.user.addresses := by
  simp only [AddressChoicePlan.attempt,missing,Option.isSome_none,Bool.false_eq_true,↓reduceIte,
    show (AllocationAddressKind.liveData == .dead) = false from rfl,
    show (AllocationAddressKind.liveData == .typeId) = false from rfl,
    Bool.not_true,Bool.or_false,representation.managed,bne_self_eq_false,representation.current,
    show (AddressMemoryKind.other == .stack) = false from rfl] at fitted
  rcases fitted with ⟨input,supported,head,tail⟩
  cases supported with
  | bernoulli _ _ reuse validFalse probability support =>
    cases reuse with
    | false =>
      have legal : Supported (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse false) :=
        .bernoulli .reuse _ false validFalse probability support
      have allowed := ChoiceFloatSupport.allowed_of_supported .reuse _ false
        representation.reuseRateLower representation.reuseRateUpper legal
      have prepared := (ReuseTake.no_reuse generation.reusePool info.size info.align
        (UInt32.ofNat before.machine.threads.activeThread.toNat) false 0 allowed).1
      simp only [fits_pad,AddressChoicePlan.select,prepared] at tail
      rcases tail with ⟨input,supported,second,rest⟩
      cases supported with
      | index _ _ value bound =>
        have next : (ChoiceExecution.tapeAccess.get before.machine).inputs[(ChoiceExecution.tapeAccess.get before.machine).cursor+1]? =
          some (.index .addressSlack value) := second
        obtain ⟨tag,final,actual,memory,threads,tape,successor,_taggedPost⟩ := RelocationRoot.memory_no_reuse before generation representation
          hooks externStatic tracker provenance offset source info value descriptor enabled tagRoom missing metadata
          notDead notType live noRace alignment strict legal head next bound (room _) positive width
        refine ⟨_,final,actual,memory,threads,?_,?_,?_⟩
        · have reset : ({before.machine.user.addresses with generation := some generation} : GlobalAddressState) =
              before.machine.user.addresses := by rw [←representation.current]
          simp only [bound,↓reduceDIte,reset,AddressChoicePlan.afterAssignment,successor] at rest
          simpa only [BoolKind.site,IndexKind.site,←tape] using rest
        · rw [tape]; exact strict
        · apply final_representation before generation provenance.allocId _ _ representation.current
            representation.managed final tracker (by obtain ⟨global,actual,enabled,race,runtime,context⟩ := _taggedPost; exact ⟨global,_,actual,enabled,race,runtime,context⟩) memory successor
          exact AddressPost.no_reuse_representation before generation representation provenance.allocId info
            (UInt32.ofNat before.machine.threads.activeThread.toNat) ⟨value,bound⟩ missing
            (.global _ descriptor rfl) live metadata allowed
            (RawGenerator.normalized_exponent info.align alignment.choose alignment.choose_spec.2)
            (room _) positive
    | true =>
      have legalReuse : Supported (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse true) :=
        .bernoulli .reuse _ true validFalse probability support
      rcases tail with ⟨input,supported,crossHead,tail⟩
      cases supported with
      | bernoulli _ _ cross crossValid crossProbability crossSource =>
        have legalCross : Supported (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits)
            (.boolean .addressCrossThread cross) :=
          .bernoulli .crossThread _ cross crossValid crossProbability crossSource
        have next : (ChoiceExecution.tapeAccess.get before.machine).inputs[(ChoiceExecution.tapeAccess.get before.machine).cursor+1]? =
            some (.boolean .addressCrossThread cross) := crossHead
        have reuseAllowed := ChoiceFloatSupport.allowed_of_supported .reuse _ true
          representation.reuseRateLower representation.reuseRateUpper legalReuse
        have crossAllowed := ChoiceFloatSupport.allowed_of_supported .crossThread _ cross
          representation.crossRateLower representation.crossRateUpper legalCross
        obtain ⟨bytes,abiBytes,normalized⟩ := alignment
        obtain ⟨bucket,present,prepared⟩ := ReuseEnsure.prepare generation.reusePool info.size info.align bytes
          (UInt32.ofNat before.machine.threads.activeThread.toNat) cross abiBytes normalized reuseAllowed crossAllowed
        let range := ReuseCandidate.candidate bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross
        change generation.reusePool.prepareTakeAddr true cross info.size info.align .other
          (UInt32.ofNat before.machine.threads.activeThread.toNat) =
          ⟨(reuse_actual ".ReusePool.ensureSubpool") generation.reusePool info.align.pow2,
            .ok (if range.2 == range.1 then none else some range)⟩ at prepared
        by_cases empty : range.2 = range.1
        · simp only [empty,beq_self_eq_true,↓reduceIte] at prepared
          simp only [AddressChoicePlan.select,prepared] at tail
          rcases tail with ⟨input,supported,thirdHead,rest⟩
          cases supported with
          | index _ _ value bound =>
            have last : (ChoiceExecution.tapeAccess.get before.machine).inputs[(ChoiceExecution.tapeAccess.get before.machine).cursor+2]? =
                some (.index .addressSlack value) := by simpa only [advance,Nat.add_assoc,Nat.reduceAdd,IndexKind.site,BoolKind.site] using thirdHead
            obtain ⟨tag,final,actual,memory,threads,tape,successor,_taggedPost⟩ := RelocationRoot.memory_reuse_empty before generation representation
              hooks externStatic tracker provenance offset source info bucket bytes cross value descriptor enabled tagRoom missing metadata
              notDead notType live noRace present empty abiBytes normalized strict legalReuse legalCross head next last bound (room _) positive width
            refine ⟨_,final,actual,memory,threads,?_,?_,?_⟩
            · simp only [bound,↓reduceDIte,AddressChoicePlan.afterAssignment,successor] at rest
              simpa only [BoolKind.site,IndexKind.site,←tape] using rest
            · rw [tape]; exact strict
            · let preparedGen := {generation with reusePool :=
                  (reuse_actual ".ReusePool.ensureSubpool") generation.reusePool info.align.pow2}
              let preparedState := AddressPost.withAddresses before
                {before.machine.user.addresses with generation := some preparedGen}
              have preparedRep : InputDraft.GenerationRepresentation preparedState preparedGen :=
                AddressPost.ensure_representation before generation representation info.align.pow2
              apply final_representation preparedState preparedGen provenance.allocId _ _ rfl
                representation.managed final tracker (by obtain ⟨global,actual,enabled,race,runtime,context⟩ := _taggedPost; exact ⟨global,_,actual,enabled,race,runtime,context⟩) memory successor
              apply AddressPost.empty_representation preparedState preparedGen preparedRep provenance.allocId info
                (UInt32.ofNat before.machine.threads.activeThread.toNat) bucket bytes cross 0 ⟨value,bound⟩ missing
                (.global _ descriptor rfl) live metadata present abiBytes normalized
              · simpa only [preparedGen,(ReuseEnsure.rates generation.reusePool info.align.pow2).1] using reuseAllowed
              · simpa only [preparedGen,(ReuseEnsure.rates generation.reusePool info.align.pow2).2] using crossAllowed
              · exact empty
              · exact room _
              · exact positive
        · have bounded : info.align.pow2 < generation.reusePool.pool.size := by
            by_cases bounded : info.align.pow2 < generation.reusePool.pool.size
            · exact bounded
            · have absent := ReuseEnsure.empty_at generation.reusePool info.align.pow2 (by omega)
              have bucketEmpty : bucket = #[] := Option.some.inj (present.symm.trans absent)
              subst bucket
              exact False.elim (empty (ReuseCandidate.empty info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross))
          have oldPresent := present
          rw [ReuseTake.ensure_present generation.reusePool info.align.pow2 bounded] at oldPresent prepared
          simp only [show (range.2 == range.1) = false from by simpa using empty,Bool.false_eq_true,↓reduceIte] at prepared
          simp only [AddressChoicePlan.select,prepared] at tail
          rcases tail with ⟨input,supported,thirdHead,rest⟩
          cases supported with
          | index _ _ value bound =>
            have last : (ChoiceExecution.tapeAccess.get before.machine).inputs[(ChoiceExecution.tapeAccess.get before.machine).cursor+2]? =
                some (.index .addressPool value) := by simpa only [advance,Nat.add_assoc,Nat.reduceAdd,IndexKind.site,BoolKind.site] using thirdHead
            obtain ⟨tag,base,final,actual,memory,threads,tape,successor,_taggedPost⟩ := RelocationRoot.memory_reuse_pool before generation representation
              hooks externStatic tracker provenance offset source info bucket cross value descriptor enabled tagRoom missing metadata
              notDead notType live noRace ⟨bytes,abiBytes,normalized⟩ oldPresent strict legalReuse legalCross
              head next last bound width
            refine ⟨_,final,actual,memory,threads,?_,?_,?_⟩
            · have reset : ({before.machine.user.addresses with generation := some generation} : GlobalAddressState) =
                  before.machine.user.addresses := by rw [←representation.current]
              dsimp only [range] at rest
              simp only [reset,AddressChoicePlan.afterAssignment,successor] at rest
              simpa only [BoolKind.site,IndexKind.site,←tape] using rest
            · rw [tape]; exact strict
            · have lower : range.1 ≤ range.1+value := by omega
              have upper : range.1+value < range.2 := by
                have ordered := (ReuseCandidate.range_spec bucket info.size
                  (UInt32.ofNat before.machine.threads.activeThread.toNat) cross).1
                change value < range.2-range.1 at bound
                change range.1 ≤ range.2 at ordered
                omega
              have aligned : ∀ row ∈ bucket, row.address % bytes = 0 := by
                intro row member
                have bucketEq := (Array.getElem?_eq_some_iff.mp oldPresent).2
                have exponent := RawGenerator.normalized_exponent info.align bytes normalized
                have canonical := (RawGenerator.align_metadata info.align exponent).1
                have bytesEq : bytes = RawGenerator.alignment info.align := by
                  rw [abiBytes] at canonical
                  exact Except.ok.inj canonical
                have alignRow := representation.poolAlignment info.align.pow2 bounded row
                  (by simpa only [bucketEq] using member)
                apply UInt64.toNat_inj.mp
                change (row.address % bytes).toNat = 0
                rw [bytesEq,UInt64.toNat_mod,RawGenerator.alignment_nat info.align exponent]
                exact alignRow
              apply final_representation before generation provenance.allocId _ _ representation.current
                representation.managed final tracker (by obtain ⟨global,actual,enabled,race,runtime,context⟩ := _taggedPost; exact ⟨global,_,actual,enabled,race,runtime,context⟩) memory successor
              exact AddressPost.reuse_representation before generation representation provenance.allocId info
                (UInt32.ofNat before.machine.threads.activeThread.toNat) bucket bytes cross (range.1+value)
                ⟨0,by decide⟩ missing (.global _ descriptor rfl) live metadata oldPresent abiBytes normalized
                reuseAllowed crossAllowed lower upper aligned

theorem memory_choices {budget : Nat} (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (hooks : ChoiceExecution.H)
    (externStatic : Miri.MIR.DefId → MachineAddress.M MiriMemoryKind ChoiceExecution.Payload (Pointer Provenance))
    (tracker : MachineHooks.BorrowState) (provenance : CtfeProvenance) (offset : UInt64)
    (source : Allocation CtfeProvenance Unit) (info : AllocationInfo)
    (nextPlan : GlobalAddressState → Plan budget)
    (descriptor : before.machine.memory.findGlobal? provenance.allocId = some
      ⟨provenance.allocId,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (enabled : before.machine.borrowTracker = some tracker)
    (tagRoom : tracker.global.nextPointerTag.value.toNat + 1 < 2^64)
    (missing : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == provenance.allocId) = none)
    (metadata : before.machine.memory.getAllocInfo provenance.allocId = .ok info)
    (notDead : info.kind ≠ .dead) (notType : info.kind ≠ .typeId)
    (live : before.machine.memory.isAllocLive provenance.allocId = true)
    (noRace : before.machine.dataRace = none)
    (alignment : InputDraft.AlignmentRepresentation info.align)
    (room : ∀ slack, RawGenerator.Room generation.generator info.size info.align slack)
    (positive : 0 < generation.generator.nextBaseAddr.toNat)
    (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩)
    (supply : Environment (AddressChoicePlan.attempt before.machine.user.addresses provenance.allocId
      ⟨.liveData,true,info.size,info.align,some .other,UInt32.ofNat before.machine.threads.activeThread.toNat⟩ nextPlan)
      (ChoiceExecution.tapeAccess.get before.machine)) :
    ∃ pointer final, PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks externStatic
      (Pointer.new provenance (Size.ofBytes offset)) before.machine = .ok pointer final ∧
      final.memory = before.machine.memory ∧ final.threads = before.machine.threads := by
  obtain ⟨pointer,final,actual,memory,threads,_tail,_strict,_post⟩ := memory_fits before generation representation hooks externStatic tracker provenance offset source info nextPlan
    descriptor enabled tagRoom missing metadata notDead notType live noRace alignment room positive width
    supply.strict supply.fits
  exact ⟨pointer,final,actual,memory,threads⟩
end EmptyFunction.RelocationEntry
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RelocationEntry.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved relocation entry axiom {dependency} in {name}"
