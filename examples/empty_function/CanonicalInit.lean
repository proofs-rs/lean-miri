import empty_function.Init
import empty_function.MetadataBinding
import empty_function.UnitRetag
import empty_function.AbiInit
import empty_function.BodyPlaceDictionaries
import empty_function.BodyAssignment

namespace EmptyFunction.CanonicalInit
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.Concurrency
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem push_actual (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p) (capacity : 0 < s.capacity)
    (continuation : ReturnContinuation) :
    ∃ frame machine,
      (ExecutionMachine.callHooks s.cfg s.limits).pushRaw () s.functionInstance s.loaded
        p.destination continuation p.before =
        .ok () (⟨⟨p.before.stack.frames.push frame⟩,machine⟩ : State) ∧
      (∃ previous, machine = FrameRelevance.pushedMachine p.before.stack.frames frame previous
        (s.cfg.lifecycle.freshLocalsIdentity p.before.machine).1) ∧
      frame.extra.borrowTracker = some {} ∧ frame.extra.dataRace = none ∧
      frame.body = s.loaded.body ∧ frame.bodyIdentity = s.loaded.identity ∧
      frame.functionInstance = s.functionInstance ∧ frame.location = .unwinding metadata.preamble ∧
      frame.returnContinuation = continuation ∧ frame.returnPlace = p.destination ∧
      frame.locals = #[{value := .dead,layout := none}] ∧ frame.vaList = #[] ∧
      frame.trackCallerArg = none ∧
      machine.borrowTracker = p.before.machine.borrowTracker ∧ machine.dataRace = none := by
  have fields := MetadataBinding.fields s metadata capacity
  obtain ⟨definitionIndex, definition, definitionResolved, definitionAt⟩ := metadata.frameDefinition
  let frame := EmptyFunction.Init.created s.cfg.lifecycle p.before s.loaded s.functionInstance p.destination
    continuation metadata.preamble s.prepared.compiler.lifecycle.frames s.options.userRelevantCrates definition
  let machine := (s.cfg.lifecycle.freshLocalsIdentity p.before.machine).1
  have threads : machine.threads = p.before.machine.threads := by
    simp only [machine, fields.freshLocalsIdentity]
  have active : machine.threads.activeThread? = some input.thread := by
    rw [threads]
    exact input.active
  have select : ∃ index old,
      FrameRelevance.top ⟨p.before.stack.frames.push frame⟩ input.thread.topUserRelevantFrame = some index ∧
      (p.before.stack.frames.push frame)[index]? = some old := by
    cases cache : input.thread.topUserRelevantFrame with
    | none =>
      refine ⟨p.before.stack.frames.size,frame,?_,?_⟩
      · simp [FrameRelevance.top,cache]
      · simp
    | some index =>
      have bounded := input.relevance index cache
      refine ⟨index,p.before.stack.frames[index],?_,?_⟩
      · simp [FrameRelevance.top,cache]
      · rw [Array.getElem?_push, if_neg (Nat.ne_of_lt bounded), Array.getElem?_eq_getElem bounded]
  obtain ⟨index,old,cached,selected⟩ := select
  have pushed := EmptyFunction.Init.push_raw s.cfg.lifecycle p.before s.loaded s.functionInstance p.destination
    continuation metadata.preamble s.prepared.compiler.lifecycle.frames s.options.userRelevantCrates definition definitionIndex
    s.prepared.compiler.lifecycle.lifecycle metadata.loweredBody fields.frameCompiler fields.preambleSpan
    fields.requiredConstants metadata.frameInlineAttribute metadata.frameTrackCaller definitionResolved definitionAt
    metadata.lifecycleBody metadata.bodyContents metadata.lifecycleRow input.thread index active old cached selected
  refine ⟨frame,FrameRelevance.pushedMachine p.before.stack.frames frame old machine,?_,⟨old,rfl⟩,?_,?_,?_⟩
  · change CallMachine.pushRaw s.cfg.lifecycle s.cfg.compiler.debugAssertions s.functionInstance s.loaded
      p.destination continuation p.before = _
    rw [fields.debug,profile.debug]
    exact pushed
  · simp only [frame,EmptyFunction.Init.created,CompilerFrameMetadata.resolvedFrame]
    have enabled := input.world.enabled
    simp only [machine,fields.freshLocalsIdentity] at *
    simp [enabled]
  · simp [frame,EmptyFunction.Init.created,CompilerFrameMetadata.resolvedFrame, fields.freshLocalsIdentity, runtime.noRace]
  · have count : s.loaded.body.locals.size = 1 := by rw [metadata.body]; exact Program.one_local
    simp only [frame,EmptyFunction.Init.created,CompilerFrameMetadata.resolvedFrame,EmptyFunction.Init.raw,Frame.create,count,
      Array.replicate_succ,Array.replicate_zero]
    simp [FrameRelevance.pushedMachine,machine,fields.freshLocalsIdentity,runtime.noRace]
    split <;> constructor <;> rfl

 theorem memory_core (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (place : MPlaceTy Provenance) (continuation : ReturnContinuation) :
    Call.initStackFrame (ExecutionMachine.callHooks s.cfg s.limits) () s.functionInstance
      s.loaded s.abi #[] false (.memory place) continuation =
      Call.zeroCore (ExecutionMachine.callHooks s.cfg s.limits) () s.functionInstance s.loaded s.abi
        place continuation := by
  let hooks := ExecutionMachine.callHooks s.cfg s.limits
  have memory : hooks.placeToOp () (.memory place) = pure ⟨.indirect place.mplace,place.layout⟩ := by rfl
  have variadic : hooks.abiVariadic s.abi = false := metadata.notVariadic
  have convention : hooks.sameConvention s.abi s.abi = true := by
    change (s.abi.conv == s.abi.conv) = true
    exact beq_self_eq_true _
  have arguments : hooks.abiArgs s.abi = #[] := metadata.noArguments
  have ret : hooks.abiReturn s.abi = s.abi.ret := rfl
  have count : s.loaded.body.argumentCount = 0 := by rw [metadata.body]; exact Program.no_arguments
  exact Call.zero_entry_core hooks () s.functionInstance s.loaded s.abi place continuation
    (MetadataBinding.caller_location s metadata capacity) (MetadataBinding.instance_abi s metadata capacity)
    (MetadataBinding.target_features s metadata capacity) memory (MetadataBinding.not_closure s metadata capacity)
    variadic convention arguments ret count

 theorem integer_protection (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (place : MPlaceTy Provenance) (layout : place.layout = s.abi.ret.layout)
    (integer : place.mplace.ptr.provenance = none)
    (noMeta : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none)
    (state : State) (tracker : MachineHooks.BorrowState)
    (enabled : state.machine.borrowTracker = some tracker)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) :
    (ExecutionMachine.callHooks s.cfg s.limits).protectArgument () place state =
      .ok () {state with machine := UnitRetag.allocatedMachine state.machine tracker room} := by
  have fields := MetadataBinding.fields s metadata capacity
  obtain ⟨pointers,globals,resolve,_,_,_⟩ := fields.pointerDictionaries
  have sized : place.layout.layout.isSized = true := by rw [layout]; exact metadata.unitSized
  have size : s.cfg.retag.sizeAndAlign place = pure (some (Size.ZERO,Align.ONE)) := by
    simpa only [layout,metadata.unitSize,metadata.unitAlign] using fields.sizeAndAlign place sized
  have unitLayout : localMemoryLayout place.layout =
      ⟨Size.ZERO,Align.ONE,.Memory (sized := true),some place.layout.ty⟩ := by
    simp [localMemoryLayout,layout,metadata.unitSize,metadata.unitAlign,metadata.unitBackend]
  have target : s.cfg.access.runtime.pointerSizeIn s.cfg.access.runtime.defaultAddressSpace =
      .ok s.cfg.access.runtime.pointerSize := by
    simp [RuntimeTargetDataLayout.pointerSizeIn,RuntimeTargetDataLayout.pointerSpecIn,
      RuntimeTargetDataLayout.pointerSize,Except.pure]
    rfl
  change TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag place state = _
  exact UnitRetag.protect_integer s.cfg.retag s.limits.retag place s.cfg.access pointers
    fields.checkPtrAccess resolve size fields.log integer state tracker enabled room unitLayout
    noMeta aligned s.cfg.access.runtime.pointerSize target
    (by intro machine; rw [fields.retainTouched]) fields.writeUninit
 theorem return_compatibility (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity) :
    (ExecutionMachine.callHooks s.cfg s.limits).checkArgumentCompat () s.abi.ret s.abi.ret = pure true := by
  have fields := MetadataBinding.fields s metadata capacity
  change s.cfg.calls.compiler.checkArgumentCompat () s.abi.ret s.abi.ret = _
  rw [fields.callsCompiler]
  change LayoutCompat.checkArgumentCompat _ _ s.abi.ret s.abi.ret = _
  exact AbiInit.unit_same _ _ _ metadata.unitIgnored metadata.unitBackend

 theorem local_span (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (machine : MachineHooks.MachineState MiriMemoryKind Configuration.RootUser)
    (identity : frame.bodyIdentity = s.loaded.identity) (function : frame.functionInstance = s.functionInstance)
    (body : frame.body = s.loaded.body) :
    (ExecutionMachine.callHooks s.cfg s.limits).localSpan s.loaded.body 0
      (LocalUnit.current frames frame machine) =
      .ok metadata.localSpan (LocalUnit.current frames frame machine) := by
  obtain ⟨remaining,eq⟩ : ∃ n : Nat, s.capacity = n+1 := ⟨s.capacity-1,by omega⟩
  have fields := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options)
    (Configuration.leaves s.prepared s.options.place.debugAssertions) remaining metadata.construction s.cfg
    (by simpa only [Configuration.rootConfig,eq] using s.built)
  obtain ⟨decl,declaration,indexed⟩ := metadata.localSourceSpan
  have bounded := metadata.compilerLocalSourceSpans metadata.loweredBody
    (Array.mem_of_getElem? metadata.bodyRow) decl (Array.mem_of_getElem? declaration)
  rw [indexed] at bounded
  change s.cfg.compiler.localSpan s.loaded.body 0 _ = _
  rw [fields.localSpan]
  exact CompilerFrameContext.localSpan_known s.prepared.compiler s.loaded metadata.loweredBody
    s.functionInstance decl metadata.localSpan metadata.bodyRow metadata.bodyContents metadata.loader
    declaration indexed bounded frames frame machine identity function body

 theorem push_done (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (machine : MachineHooks.MachineState MiriMemoryKind Configuration.RootUser)
    (body : frame.body = s.loaded.body)
    (locals : frame.locals = #[{value := .dead,layout := none}])
    (noClocks : frame.extra.dataRace = none) :
    (ExecutionMachine.callHooks s.cfg s.limits).pushDone () (LocalUnit.current frames frame machine) =
      .ok () (LocalUnit.current frames {frame with
        locals := #[{value := .live (.immediate .uninit),layout := none}], location := .mir .start} machine) := by
  have fields := MetadataBinding.fields s metadata capacity
  have types : frame.body.locals = #[s.abi.ret.layout.ty] := by
    rw [body]; exact BodyAssignment.raw_unit_local s metadata
  have trivial : s.cfg.lifecycle.storage.veryTriviallySized s.abi.ret.layout.ty = .ok true := by
    rw [fields.storageSized]; exact metadata.unitStorageSized
  have live := LocalUnit.storage_live_zero s.cfg.lifecycle.storage frames frame machine s.abi.ret.layout.ty
    locals types trivial noClocks
  have vars : CallMachine.alwaysLiveVarsAndTemps frame.body = .ok #[] := by
    rw [body,metadata.body]; rfl
  have blocks : frame.body.basicBlocks.size = 1 := by rw [body,metadata.body]; exact Program.one_block
  change CallMachine.pushDone s.cfg.lifecycle (LocalUnit.current frames frame machine) = _
  unfold CallMachine.pushDone
  simp only [bind,EStateM.bind]
  rw [live]
  simp [LocalUnit.current,MachineHooks.currentFrame,Stack.currentFrame?,vars,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
    Stack.updateCurrentLocation,Frame.setLocation,blocks,Location.start,
    set,MonadStateOf.set,EStateM.set,Except.bind,Except.pure,Array.set_push]

 def spanAt (span : SpanRef) : MachineHooks.M MiriMemoryKind Configuration.RootUser Unit := do
  let frame ← MachineHooks.currentFrame
  MachineHooks.setCurrentFrame {frame with location := .unwinding span}
 def normalizedContinuation (s : Static) (continuation : ReturnContinuation) : ReturnContinuation :=
  if s.abi.canUnwind then continuation else
    match continuation with
    | .stop _ => continuation
    | .goto target _ => .goto target .Unreachable
 def rawCore (s : Static) (place : MPlaceTy Provenance) (continuation : ReturnContinuation) :
    MachineHooks.M MiriMemoryKind Configuration.RootUser Unit := do
  let hooks := ExecutionMachine.callHooks s.cfg s.limits
  hooks.pushRaw () s.functionInstance s.loaded (.memory place) (normalizedContinuation s continuation)
  let frame ← MachineHooks.currentFrame
  let preamble ← match frame.location with
    | .unwinding span => pure span
    | .mir _ => throw (StepError.invalidProgram "raw frame does not have preamble location")
  MachineHooks.setCurrentFrame {frame with trackCallerArg := none}
  spanAt (← hooks.localSpan s.loaded.body 0)
  hooks.protectArgument () place
  spanAt preamble
  hooks.pushDone ()
 theorem core_reduction (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (place : MPlaceTy Provenance) (continuation : ReturnContinuation) :
    Call.zeroCore (ExecutionMachine.callHooks s.cfg s.limits) () s.functionInstance s.loaded s.abi
      place continuation = rawCore s place continuation := by
  let hooks := ExecutionMachine.callHooks s.cfg s.limits
  have mode : hooks.withRetagMode () .FnEntry (pure ((0,0) : Nat × Nat)) = pure (0,0) := by
    funext state
    exact Init.mode_pure .FnEntry ((0,0) : Nat × Nat) state
  have compatible : hooks.checkArgumentCompat () s.abi.ret s.abi.ret = pure true :=
    return_compatibility s metadata capacity
  have after : hooks.afterFrameInit () = pure () := rfl
  change Call.zeroCore hooks () s.functionInstance s.loaded s.abi place continuation = _
  unfold Call.zeroCore rawCore
  simp only [mode,compatible,after,bind_pure_comp,bind_assoc,pure_bind]
  with_unfolding_all rfl

 theorem set_current (frames : Array LocalUnit.F) (frame next : LocalUnit.F)
    (machine : MachineHooks.MachineState MiriMemoryKind Configuration.RootUser) :
    MachineHooks.setCurrentFrame next (LocalUnit.current frames frame machine) =
      .ok () (LocalUnit.current frames next machine) := by
  simp [MachineHooks.setCurrentFrame,LocalUnit.current,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
    set,MonadStateOf.set,EStateM.set]
 theorem span_current (span : SpanRef) (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (machine : MachineHooks.MachineState MiriMemoryKind Configuration.RootUser) :
    spanAt span (LocalUnit.current frames frame machine) =
      .ok () (LocalUnit.current frames {frame with location := .unwinding span} machine) := by
  simp [spanAt,MachineHooks.currentFrame,MachineHooks.setCurrentFrame,LocalUnit.current,Stack.currentFrame?,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
    set,MonadStateOf.set,EStateM.set]

 theorem get_current (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (machine : MachineHooks.MachineState MiriMemoryKind Configuration.RootUser) :
    MachineHooks.currentFrame (LocalUnit.current frames frame machine) =
      .ok frame (LocalUnit.current frames frame machine) := by
  simp [MachineHooks.currentFrame,LocalUnit.current,Stack.currentFrame?,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]


 def initializedMachine (s : Static) (p : Packet) (frame previous : LocalUnit.F)
    (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) :=
  UnitRetag.allocatedMachine
    (FrameRelevance.pushedMachine p.before.stack.frames frame previous
      (s.cfg.lifecycle.freshLocalsIdentity p.before.machine).1) tracker room
 theorem init_integer (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    {choiceCondition : Prop} (resources : ResourceMargins s p choiceCondition)
    (destination : InputDraft.MemoryDestination s p input.tracker)
    (integer : destination.place.mplace.ptr.provenance = none) :
    ∃ frame machine,
      WholeCall.install s p = .ok () (LocalUnit.current p.before.stack.frames frame machine) ∧
      frame.body = s.loaded.body ∧ frame.bodyIdentity = s.loaded.identity ∧
      frame.functionInstance = s.functionInstance ∧ frame.location = .mir ⟨0,0⟩ ∧
      frame.locals = #[{value := .live (.immediate .uninit),layout := none}] ∧
      frame.extra.borrowTracker = some {} ∧ frame.extra.dataRace = none ∧
      frame.returnPlace = p.destination ∧
      frame.returnContinuation = normalizedContinuation s (.goto (some p.returnBlock) p.unwind) ∧
      frame.vaList = #[] ∧
      machine.user.payload.ghost = false ∧ machine.user.payload.validation = .Shallow ∧
      ∃ (previous : LocalUnit.F) (room : input.tracker.global.nextPointerTag.value < 18446744073709551615),
        machine = initializedMachine s p frame previous input.tracker room := by
  have budget : 64 ≤ resources.budget := by
    have bound := resources.reserve
    unfold work at bound
    omega
  have capacity : 0 < s.capacity := by have bound := resources.capacity; omega
  have room : input.tracker.global.nextPointerTag.value < 18446744073709551615 := by
    have bound := resources.tagRoom input.tracker input.world.enabled
    change input.tracker.global.nextPointerTag.value.toNat < 18446744073709551615
    omega
  let continuation : ReturnContinuation := .goto (some p.returnBlock) p.unwind
  obtain ⟨frame,machine,push,⟨previous,machineEq⟩,tracked,noClocks,body,identity,function,location,
    returning,returnPlace,locals,varargs,callerArg,machineTracker,machineRace⟩ :=
      push_actual s metadata profile p runtime input capacity (normalizedContinuation s continuation)
  have pushMemory := push
  rw [destination.encoding] at pushMemory
  have cleared : {frame with trackCallerArg := none} = frame := by rw [←callerArg]
  have localQuery := local_span s metadata capacity p.before.stack.frames frame machine identity function body
  have enabled : machine.borrowTracker = some input.tracker := machineTracker.trans input.world.enabled
  let changed := UnitRetag.allocatedMachine machine input.tracker room
  have protect := integer_protection s metadata capacity destination.place destination.layout integer
    destination.sizedMetadata destination.alignmentCache
    (LocalUnit.current p.before.stack.frames {frame with location := .unwinding metadata.localSpan} machine)
    input.tracker enabled room
  have done := push_done s metadata capacity p.before.stack.frames frame changed body locals noClocks
  have restored : {{frame with location := .unwinding metadata.localSpan} with
      location := .unwinding metadata.preamble} = frame := by rw [←location]
  have result : rawCore s destination.place continuation p.before =
      .ok () (LocalUnit.current p.before.stack.frames {frame with
        locals := #[{value := .live (.immediate .uninit),layout := none}],location := .mir .start} changed) := by
    unfold rawCore
    simp only [bind,EStateM.bind]
    rw [pushMemory]
    change (do
      let current ← MachineHooks.currentFrame
      let preamble ← match current.location with
        | .unwinding span => pure span
        | .mir _ => throw (StepError.invalidProgram "raw frame does not have preamble location")
      MachineHooks.setCurrentFrame {current with trackCallerArg := none}
      spanAt (← (ExecutionMachine.callHooks s.cfg s.limits).localSpan s.loaded.body 0)
      (ExecutionMachine.callHooks s.cfg s.limits).protectArgument () destination.place
      spanAt preamble
      (ExecutionMachine.callHooks s.cfg s.limits).pushDone ())
      (LocalUnit.current p.before.stack.frames frame machine) = _
    simp only [bind,EStateM.bind]
    rw [get_current]
    simp only [location,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
    rw [set_current]
    simp only [←location,cleared]
    rw [localQuery]
    dsimp only
    rw [span_current]
    dsimp only
    rw [protect]
    change (do
      spanAt metadata.preamble
      (ExecutionMachine.callHooks s.cfg s.limits).pushDone ())
      (LocalUnit.current p.before.stack.frames {frame with location := .unwinding metadata.localSpan} changed) = _
    simp only [bind,EStateM.bind]
    rw [span_current]
    dsimp only
    rw [restored]
    exact done
  refine ⟨{frame with
      locals := #[{value := .live (.immediate .uninit),layout := none}]
      location := .mir .start},changed,?_,?_⟩
  · unfold WholeCall.install
    rw [destination.encoding, memory_core s metadata capacity,core_reduction s metadata capacity]
    exact result
  · refine ⟨body,identity,function,rfl,rfl,tracked,noClocks,returnPlace,returning,varargs,?_,?_,
      previous,room,?_⟩
    · simp [changed,UnitRetag.allocatedMachine,machineEq,FrameRelevance.pushedMachine,
        (MetadataBinding.fields s metadata capacity).freshLocalsIdentity]
      split <;> change p.before.machine.user.payload.ghost = false
      all_goals exact runtime.ghost
    · simp [changed,UnitRetag.allocatedMachine,machineEq,FrameRelevance.pushedMachine,
        (MetadataBinding.fields s metadata capacity).freshLocalsIdentity]
      split <;> change p.before.machine.user.payload.validation = .Shallow
      all_goals exact runtime.shallow
    · dsimp only [initializedMachine,changed]
      rw [machineEq]
      rfl
end EmptyFunction.CanonicalInit
