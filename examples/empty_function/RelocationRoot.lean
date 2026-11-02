import empty_function.AddressRacePost
import empty_function.ChoiceProjection
import Miri.Interpreter.PointerSource
import empty_function.RelocationChoices
namespace EmptyFunction.RelocationRoot
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Actual first-root tag construction from raw counter room. Both cached and
uncached runtime target IDs are admitted, with no compiler raw-ID conflation. -/
theorem root_tag_room (global : GlobalState) (id : AllocId)
    (room : global.nextPointerTag.value.toNat + 1 < 2^64) :
    ∃ after tag, global.rootPointerTag id = .ok (after,tag) ∧
      after.protectedTags = global.protectedTags ∧
      after.trackedPointerTags = global.trackedPointerTags := by
  cases cached : global.rootTag? id with
  | some tag => exact ⟨global,tag,GlobalState.rootPointerTag_existing global id tag cached,rfl,rfl⟩
  | none =>
    have notMax : global.nextPointerTag.value ≠ 18446744073709551615 := by
      intro maximum
      rw [maximum] at room
      contradiction
    have nonzero : global.nextPointerTag.value + 1 ≠ 0 := by
      intro zero
      have actual : (global.nextPointerTag.value+1).toNat = global.nextPointerTag.value.toNat+1 := by
        rw [UInt64.toNat_add]
        change (global.nextPointerTag.value.toNat+1) % 2^64 = _
        exact Nat.mod_eq_of_lt room
      rw [zero] at actual
      change 0 = _ at actual
      omega
    let successor : BorTag := ⟨global.nextPointerTag.value+1,nonzero⟩
    let after : GlobalState := {global with
      nextPointerTag := successor
      rootPointerTags := global.rootPointerTags.push (id,global.nextPointerTag)}
    refine ⟨after,global.nextPointerTag,?_,rfl,rfl⟩
    simp [after,successor,GlobalState.rootPointerTag,GlobalState.newPointerTag,cached,
      BorTag.succ,notMax,BorTag.ofUInt64,nonzero,bind,Except.bind,pure,Except.pure]
open Lean Elab Tactic
private def target64 : Miri.Memory.PointerArithmetic := ⟨Size.ofBytes 8⟩

private def findUniquePrivate (suffix : String) : TacticM Name := do
  let env ← getEnv
  let candidates := env.constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match candidates with
  | [name] => pure name
  | _ => throwError m!"expected one private definition `{suffix}`, found {candidates.length}"

elab "simp_relocation_pointer_64" : tactic => do
  let helpers ← [
    ".PointerArithmetic.sizeResult",
    ".PointerArithmetic.toUInt64Checked",
    ".Size.integerWidth"
  ].mapM findUniquePrivate
  let helperIds := helpers.toArray.map mkIdent
  let generated ← `(tactic| simp [target64, Miri.Memory.PointerArithmetic.truncateToTargetUsize,
    Miri.ABI.Size.truncate, $[$helperIds:ident],*])
  evalTactic generated

private theorem truncate_size_eight (value : UInt64) :
    (Size.ofBytes 8).truncate (BitVec.ofNat 128 value.toNat) =
      .ok (BitVec.ofNat 128 value.toNat) := by
  have hBits : Size.bits (Size.ofBytes 8) = .ok 64 := by decide
  simp_relocation_pointer_64
  rw [hBits]
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  have hval : value.toNat < 2 ^ 64 := UInt64.toNat_lt value
  have hmod : value.toNat % 2 ^ 128 = value.toNat := Nat.mod_eq_of_lt (by omega)
  simp
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by omega)]
  simp only [BitVec.toNat_ofNat]
  rw [hmod]
  exact Nat.mod_eq_of_lt hval

theorem truncate_u64_identity (value : UInt64) :
    target64.truncateToTargetUsize value = .ok value := by
  unfold target64 Miri.Memory.PointerArithmetic.truncateToTargetUsize
  rw [truncate_size_eight]
  simp_relocation_pointer_64
  simp only [Bind.bind, Except.bind]
  have hval : value.toNat < 2 ^ 64 := UInt64.toNat_lt value
  have h128 : value.toNat < 2 ^ 128 := by omega
  simp [Except.mapError, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h128, hval, UInt64.ofNat_toNat]


variable {Prov : Type}

theorem wrapping_offset_u64 (ptr : Pointer Prov) (delta : Size) :
    ptr.wrappingOffset delta target64 =
      .ok { ptr with offset := Size.ofBytes (ptr.offset.bytes + delta.bytes) } := by
  unfold Pointer.wrappingOffset
  rw [truncate_u64_identity]
  rfl



private theorem root_address {K U : Type} (choices : ExecutionChoices.Access (MachineAddress.State K U))
    (hooks : MachineAddress.Hooks K U) (externStatic : Miri.MIR.DefId → MachineAddress.M K U (Pointer Provenance))
    (before : MachineAddress.State K U) (tracker : MachineHooks.BorrowState)
    (provenance : CtfeProvenance) (offset base : UInt64) (root : BorTag)
    (source : Allocation CtfeProvenance Unit) (global : GlobalState) (after : MachineAddress.State K U)
    (descriptor : before.memory.findGlobal? provenance.allocId = some
      ⟨provenance.allocId,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (enabled : before.borrowTracker = some tracker)
    (tagged : tracker.global.rootPointerTag provenance.allocId = .ok (global,root))
    (address : MachineAddress.addrFromAllocId choices hooks provenance.allocId (some .other)
      {before with borrowTracker := some {tracker with global}} = .ok base after)
    (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩) :
    PointerSource.globalRootPointer choices hooks externStatic (Pointer.new provenance (Size.ofBytes offset)) before =
      .ok (Pointer.new (Provenance.concrete provenance.allocId root) (Size.ofBytes (base+offset))) after := by
  simp only [PointerSource.globalRootPointer,Pointer.new,descriptor,enabled,tagged,
    get,getThe,MonadStateOf.get,EStateM.get,modify,modifyGet,
    MonadStateOf.modifyGet,EStateM.modifyGet,bind,EStateM.bind,pure,EStateM.pure,address,width]
  have wrapping := wrapping_offset_u64
    (Pointer.new (Provenance.concrete provenance.allocId root) (Size.ofBytes base)) (Size.ofBytes offset)
  simp only [Pointer.new,target64] at wrapping
  rw [wrapping]
  rfl
/-- One actual lazy compiler-memory relocation root call, including an
uncached borrow root, all legal no-reuse/slack responses, actual address
assignment and wrapping offset. Target contents may contain arbitrary relocations;
this operation does not recursively materialize them. Other choice branches
are separate theorems and remain part of the final coverage obligation. -/
theorem memory_no_reuse (before : WholeCall.State) (generation : AllocAddresses.AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (hooks : ChoiceExecution.H)
    (externStatic : Miri.MIR.DefId → MachineAddress.M MiriMemoryKind ChoiceExecution.Payload (Pointer Provenance))
    (tracker : MachineHooks.BorrowState) (provenance : CtfeProvenance) (offset : UInt64)
    (source : Allocation CtfeProvenance Unit) (info : AllocationInfo) (value : Nat)
    (descriptor : before.machine.memory.findGlobal? provenance.allocId = some
      ⟨provenance.allocId,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (enabled : before.machine.borrowTracker = some tracker)
    (tagRoom : tracker.global.nextPointerTag.value.toNat + 1 < 2^64)
    (missing : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == provenance.allocId) = none)
    (metadata : before.machine.memory.getAllocInfo provenance.allocId = .ok info)
    (notDead : info.kind ≠ .dead) (notType : info.kind ≠ .typeId)
    (live : before.machine.memory.isAllocLive provenance.allocId = true) (noRace : before.machine.dataRace = none)
    (alignment : InputDraft.AlignmentRepresentation info.align)
    (strict : (ChoiceExecution.tapeAccess.get before.machine).policy = .strict)
    (reuse : ChoiceSupply.Supported (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits)
      (.boolean .addressReuse false))
    (head : (ChoiceExecution.tapeAccess.get before.machine).inputs[(ChoiceExecution.tapeAccess.get before.machine).cursor]? =
      some (.boolean .addressReuse false))
    (next : (ChoiceExecution.tapeAccess.get before.machine).inputs[(ChoiceExecution.tapeAccess.get before.machine).cursor+1]? =
      some (.index .addressSlack value))
    (bound : value < 16)
    (room : RawGenerator.Room generation.generator info.size info.align ⟨value,bound⟩)
    (positive : 0 < generation.generator.nextBaseAddr.toNat)
    (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩) :
    ∃ tag final, PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks externStatic
      (Pointer.new provenance (Size.ofBytes offset)) before.machine =
      .ok (Pointer.new (Provenance.concrete provenance.allocId tag)
        (Size.ofBytes (RawGenerator.base generation.generator info.align ⟨value,bound⟩+offset))) final ∧
      final.memory = before.machine.memory ∧ final.threads = before.machine.threads ∧
      ChoiceExecution.tapeAccess.get final = ChoiceSupply.advance
        (ChoiceSupply.advance (ChoiceExecution.tapeAccess.get before.machine)
          (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse false))
        (.index .slack 16) (.index .addressSlack value) ∧
      AddressChoicePlan.assignedState (before.machine.user.addresses.addrFromAllocId provenance.allocId
        (some ⟨.liveData,true,info.size,info.align,some .other,UInt32.ofNat before.machine.threads.activeThread.toNat⟩)
        ⟨false,false,0,⟨value,bound⟩⟩) = .ok final.user.addresses ∧
      ∃ global, tracker.global.rootPointerTag provenance.allocId = .ok (global,tag) ∧
        final.borrowTracker = some {tracker with global} ∧ final.dataRace = before.machine.dataRace ∧
        final.user.payload.payload.user.runtime = before.machine.user.payload.payload.user.runtime ∧
        RelocationContext.view final.user.payload = RelocationContext.view before.machine.user.payload := by
  obtain ⟨global,tag,tagged,_protected,_tracked⟩ := root_tag_room tracker.global provenance.allocId tagRoom
  let rootState : ChoiceExecution.S := {before.machine with borrowTracker := some {tracker with global}}
  have allowed := ChoiceFloatSupport.allowed_of_supported .reuse _ false
    representation.reuseRateLower representation.reuseRateUpper reuse
  have demanded := RelocationChoices.no_reuse_supplied hooks rootState provenance.allocId info generation value
    missing metadata notDead notType live representation.managed representation.current strict reuse head next bound allowed
  let middle := RelocationChoices.after (RelocationChoices.after rootState
    (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse false))
    (.index .slack 16) (.index .addressSlack value)
  obtain ⟨bytes,_,normalized⟩ := alignment
  obtain ⟨final,assigned,memory,_borrow,threads,_race,payload⟩ := BumpAddress.no_reuse hooks middle
    provenance.allocId info generation ⟨value,bound⟩ missing metadata notDead notType live
    representation.managed representation.current representation.reuseRateLower representation.reuseRateUpper reuse
    (RawGenerator.normalized_exponent info.align bytes normalized) room positive
    (RawResources.frontier before generation representation)
  have successor := RelocationPost.assignment_state hooks middle provenance.allocId info ⟨false,false,0,⟨value,bound⟩⟩
    missing metadata notDead notType live representation.managed noRace _ final assigned
  refine ⟨tag,final,?_,memory,threads,?_,successor,global,tagged,_borrow,_race,(congrArg (fun payload => payload.payload.user.runtime) payload),(by have projected := congrArg RelocationContext.view payload; exact projected)⟩
  · exact root_address ChoiceExecution.tapeAccess hooks externStatic before.machine tracker provenance offset _ tag
      source global final descriptor enabled tagged (demanded.trans assigned) width
  · exact congrArg (fun payload => payload.payload.user.choices) payload
/-- The same actual compiler-memory root operation for all supported existing
hole selections, including cross-thread choices in the no-race profile. -/
theorem memory_reuse_pool (before : WholeCall.State) (generation : AllocAddresses.AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (hooks : ChoiceExecution.H)
    (externStatic : Miri.MIR.DefId → MachineAddress.M MiriMemoryKind ChoiceExecution.Payload (Pointer Provenance))
    (tracker : MachineHooks.BorrowState) (provenance : CtfeProvenance) (offset : UInt64)
    (source : Allocation CtfeProvenance Unit) (info : AllocationInfo)
    (bucket : Array AllocAddresses.ReusableAddress) (cross : Bool) (value : Nat)
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
    (present : generation.reusePool.pool[info.align.pow2]? = some bucket)
    (strict : (ChoiceExecution.tapeAccess.get before.machine).policy = .strict)
    (reuse : ChoiceSupply.Supported (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse true))
    (crossSupport : ChoiceSupply.Supported (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits)
      (.boolean .addressCrossThread cross))
    (head : (ChoiceExecution.tapeAccess.get before.machine).inputs[(ChoiceExecution.tapeAccess.get before.machine).cursor]? =
      some (.boolean .addressReuse true))
    (next : (ChoiceExecution.tapeAccess.get before.machine).inputs[(ChoiceExecution.tapeAccess.get before.machine).cursor+1]? =
      some (.boolean .addressCrossThread cross))
    (last : (ChoiceExecution.tapeAccess.get before.machine).inputs[(ChoiceExecution.tapeAccess.get before.machine).cursor+2]? =
      some (.index .addressPool value))
    (bound : value < (ReuseCandidate.candidate bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross).2 -
      (ReuseCandidate.candidate bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross).1)
    (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩) :
    ∃ tag base final, PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks externStatic
      (Pointer.new provenance (Size.ofBytes offset)) before.machine =
      .ok (Pointer.new (Provenance.concrete provenance.allocId tag) (Size.ofBytes (base+offset))) final ∧
      final.memory = before.machine.memory ∧ final.threads = before.machine.threads ∧
      ChoiceExecution.tapeAccess.get final = ChoiceSupply.advance
        (ChoiceSupply.advance (ChoiceSupply.advance (ChoiceExecution.tapeAccess.get before.machine)
          (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse true))
          (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits) (.boolean .addressCrossThread cross))
        (.index .pool ((ReuseCandidate.candidate bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross).2 -
          (ReuseCandidate.candidate bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross).1))
        (.index .addressPool value) ∧
      AddressChoicePlan.assignedState (before.machine.user.addresses.addrFromAllocId provenance.allocId
        (some ⟨.liveData,true,info.size,info.align,some .other,UInt32.ofNat before.machine.threads.activeThread.toNat⟩)
        ⟨true,cross,(ReuseCandidate.candidate bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross).1+value,⟨0,by decide⟩⟩) =
        .ok final.user.addresses ∧
      ∃ global, tracker.global.rootPointerTag provenance.allocId = .ok (global,tag) ∧
        final.borrowTracker = some {tracker with global} ∧ final.dataRace = before.machine.dataRace ∧
        final.user.payload.payload.user.runtime = before.machine.user.payload.payload.user.runtime ∧
        RelocationContext.view final.user.payload = RelocationContext.view before.machine.user.payload := by
  obtain ⟨global,tag,tagged,_protected,_tracked⟩ := root_tag_room tracker.global provenance.allocId tagRoom
  let rootState : ChoiceExecution.S := {before.machine with borrowTracker := some {tracker with global}}
  obtain ⟨bytes,abiBytes,normalized⟩ := alignment
  have reuseAllowed := ChoiceFloatSupport.allowed_of_supported .reuse _ true
    representation.reuseRateLower representation.reuseRateUpper reuse
  have crossAllowed := ChoiceFloatSupport.allowed_of_supported .crossThread _ cross
    representation.crossRateLower representation.crossRateUpper crossSupport
  have demanded := RelocationChoices.reuse_pool_supplied hooks rootState provenance.allocId info generation bucket bytes cross value
    missing metadata notDead notType live representation.managed representation.current present abiBytes normalized
    strict reuse crossSupport head next last bound reuseAllowed crossAllowed
  let range := ReuseCandidate.candidate bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross
  let middle := RelocationChoices.after (RelocationChoices.after (RelocationChoices.after rootState
    (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse true))
    (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits) (.boolean .addressCrossThread cross))
    (.index .pool (range.2-range.1)) (.index .addressPool value)
  have lower : range.1 ≤ range.1+value := by omega
  have upper : range.1+value < range.2 := by
    have ordered := (ReuseCandidate.range_spec bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross).1
    change value < range.2-range.1 at bound
    change range.1 ≤ range.2 at ordered
    omega
  obtain ⟨base,final,assigned,memory,_borrow,threads,payload⟩ := RelocationAddress.reuse_assignment_at
    before generation representation hooks middle rfl rfl provenance.allocId info bucket cross (range.1+value)
    missing metadata notDead notType live noRace present ⟨bytes,abiBytes,normalized⟩ reuse crossSupport lower upper
  have _race : final.dataRace = middle.dataRace := by
    have preservation := MachineAddress.assign_no_race hooks middle provenance.allocId (some .other)
      ⟨true,cross,range.1+value,⟨0,by decide⟩⟩ representation.managed noRace
    rw [assigned] at preservation
    exact preservation
  have successor := RelocationPost.assignment_state hooks middle provenance.allocId info ⟨true,cross,range.1+value,⟨0,by decide⟩⟩
    missing metadata notDead notType live representation.managed noRace _ final assigned
  refine ⟨tag,base,final,?_,memory,threads,?_,successor,global,tagged,_borrow,_race,(congrArg (fun payload => payload.payload.user.runtime) payload),(by have projected := congrArg RelocationContext.view payload; exact projected)⟩
  · exact root_address ChoiceExecution.tapeAccess hooks externStatic before.machine tracker provenance offset _ tag
      source global final descriptor enabled tagged (demanded.trans assigned) width
  · exact congrArg (fun payload => payload.payload.user.choices) payload
/-- The actual root operation on the empty-hole branch, including an
initially absent alignment bucket. Root tags and address slack remain arbitrary
legal source responses, and target compiler contents are never recursed into. -/
theorem memory_reuse_empty (before : WholeCall.State) (generation : AllocAddresses.AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (hooks : ChoiceExecution.H)
    (externStatic : Miri.MIR.DefId → MachineAddress.M MiriMemoryKind ChoiceExecution.Payload (Pointer Provenance))
    (tracker : MachineHooks.BorrowState) (provenance : CtfeProvenance) (offset : UInt64)
    (source : Allocation CtfeProvenance Unit) (info : AllocationInfo)
    (bucket : Array AllocAddresses.ReusableAddress) (bytes : UInt64) (cross : Bool) (value : Nat)
    (descriptor : before.machine.memory.findGlobal? provenance.allocId = some
      ⟨provenance.allocId,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (enabled : before.machine.borrowTracker = some tracker)
    (tagRoom : tracker.global.nextPointerTag.value.toNat + 1 < 2^64)
    (missing : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == provenance.allocId) = none)
    (metadata : before.machine.memory.getAllocInfo provenance.allocId = .ok info)
    (notDead : info.kind ≠ .dead) (notType : info.kind ≠ .typeId)
    (live : before.machine.memory.isAllocLive provenance.allocId = true) (noRace : before.machine.dataRace = none)
    (present : ((reuse_actual ".ReusePool.ensureSubpool") generation.reusePool info.align.pow2).pool[info.align.pow2]? = some bucket)
    (empty : (ReuseCandidate.candidate bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross).2 =
      (ReuseCandidate.candidate bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross).1)
    (abiBytes : Align.bytes info.align = .ok bytes) (normalized : Align.fromBytes bytes = .ok info.align)
    (strict : (ChoiceExecution.tapeAccess.get before.machine).policy = .strict)
    (reuse : ChoiceSupply.Supported (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse true))
    (crossSupport : ChoiceSupply.Supported (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits)
      (.boolean .addressCrossThread cross))
    (head : (ChoiceExecution.tapeAccess.get before.machine).inputs[(ChoiceExecution.tapeAccess.get before.machine).cursor]? =
      some (.boolean .addressReuse true))
    (next : (ChoiceExecution.tapeAccess.get before.machine).inputs[(ChoiceExecution.tapeAccess.get before.machine).cursor+1]? =
      some (.boolean .addressCrossThread cross))
    (last : (ChoiceExecution.tapeAccess.get before.machine).inputs[(ChoiceExecution.tapeAccess.get before.machine).cursor+2]? =
      some (.index .addressSlack value))
    (bound : value < 16)
    (room : RawGenerator.Room generation.generator info.size info.align ⟨value,bound⟩)
    (positive : 0 < generation.generator.nextBaseAddr.toNat)
    (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩) :
    ∃ tag final, PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks externStatic
      (Pointer.new provenance (Size.ofBytes offset)) before.machine =
      .ok (Pointer.new (Provenance.concrete provenance.allocId tag)
        (Size.ofBytes (RawGenerator.base generation.generator info.align ⟨value,bound⟩+offset))) final ∧
      final.memory = before.machine.memory ∧ final.threads = before.machine.threads ∧
      ChoiceExecution.tapeAccess.get final = ChoiceSupply.advance
        (ChoiceSupply.advance (ChoiceSupply.advance (ChoiceExecution.tapeAccess.get before.machine)
          (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse true))
          (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits) (.boolean .addressCrossThread cross))
        (.index .slack 16) (.index .addressSlack value) ∧
      AddressChoicePlan.assignedState
        (({before.machine.user.addresses with
          generation := some {generation with
            reusePool := (reuse_actual ".ReusePool.ensureSubpool") generation.reusePool info.align.pow2}} : AllocAddresses.GlobalAddressState).addrFromAllocId provenance.allocId
          (some ⟨.liveData,true,info.size,info.align,some .other,UInt32.ofNat before.machine.threads.activeThread.toNat⟩)
          ⟨true,cross,0,⟨value,bound⟩⟩) = .ok final.user.addresses ∧
      ∃ global, tracker.global.rootPointerTag provenance.allocId = .ok (global,tag) ∧
        final.borrowTracker = some {tracker with global} ∧ final.dataRace = before.machine.dataRace ∧
        final.user.payload.payload.user.runtime = before.machine.user.payload.payload.user.runtime ∧
        RelocationContext.view final.user.payload = RelocationContext.view before.machine.user.payload := by
  obtain ⟨global,tag,tagged,_protected,_tracked⟩ := root_tag_room tracker.global provenance.allocId tagRoom
  let rootState : ChoiceExecution.S := {before.machine with borrowTracker := some {tracker with global}}
  obtain ⟨final,address,memory,_borrow,threads,tape,successor,_race,runtime,context⟩ := RelocationChoices.reuse_empty_success_at before generation
    representation hooks rootState rfl provenance.allocId info bucket bytes cross value missing metadata notDead notType live noRace
    present empty abiBytes normalized strict reuse crossSupport head next last bound room positive
  refine ⟨tag,final,?_,memory,threads,tape,successor,global,tagged,_borrow,_race,runtime,context⟩
  exact root_address ChoiceExecution.tapeAccess hooks externStatic before.machine tracker provenance offset _ tag
    source global final descriptor enabled tagged address width
/-- Cached targets are required by repeated ordinary relocations. This real
root operation consumes no tape and leaves the complete address state unchanged. -/
theorem memory_cached (before : ChoiceExecution.S) (hooks : ChoiceExecution.H)
    (externStatic : Miri.MIR.DefId → MachineAddress.M MiriMemoryKind ChoiceExecution.Payload (Pointer Provenance))
    (tracker : MachineHooks.BorrowState) (provenance : CtfeProvenance) (offset base : UInt64)
    (source : Allocation CtfeProvenance Unit)
    (descriptor : before.memory.findGlobal? provenance.allocId = some
      ⟨provenance.allocId,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (enabled : before.borrowTracker = some tracker)
    (tagRoom : tracker.global.nextPointerTag.value.toNat + 1 < 2^64)
    (cached : before.user.addresses.baseAddr.find? (fun row => row.allocId == provenance.allocId) = some ⟨provenance.allocId,base⟩)
    (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩) :
    ∃ tag final, PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks externStatic
      (Pointer.new provenance (Size.ofBytes offset)) before =
      .ok (Pointer.new (Provenance.concrete provenance.allocId tag) (Size.ofBytes (base+offset))) final ∧
      final.memory = before.memory ∧ final.threads = before.threads ∧
      final.user.addresses = before.user.addresses ∧ ChoiceExecution.tapeAccess.get final = ChoiceExecution.tapeAccess.get before ∧
      ∃ global, tracker.global.rootPointerTag provenance.allocId = .ok (global,tag) ∧
        final.borrowTracker = some {tracker with global} ∧ final.dataRace = before.dataRace ∧
        final.user.payload.payload.user.runtime = before.user.payload.payload.user.runtime ∧
        RelocationContext.view final.user.payload = RelocationContext.view before.user.payload := by
  obtain ⟨global,tag,tagged,_protected,_tracked⟩ := root_tag_room tracker.global provenance.allocId tagRoom
  let rootState : ChoiceExecution.S := {before with borrowTracker := some {tracker with global}}
  have address : MachineAddress.addrFromAllocId ChoiceExecution.tapeAccess hooks provenance.allocId (some .other) rootState =
      .ok base rootState := by
    simp [MachineAddress.addrFromAllocId,cached,rootState,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  refine ⟨tag,rootState,?_,rfl,rfl,rfl,rfl,global,tagged,rfl,rfl,rfl,rfl⟩
  exact root_address ChoiceExecution.tapeAccess hooks externStatic before tracker provenance offset base tag source global rootState
    descriptor enabled tagged address width
end EmptyFunction.RelocationRoot
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RelocationRoot.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved relocation root axiom {dependency} in {name}"
