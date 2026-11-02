import empty_function.BodyCopy

namespace EmptyFunction.LocalImmediate
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
variable {K U C : Type}

abbrev F := LocalUnit.F

def cached (frame : F) (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout)
    (layout : LocalLayout) (bound : id < frame.locals.size) : F :=
  {frame with locals := frame.locals.set id {slot with layout := some layout} bound}

 theorem get_local (frame : F) (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout)
    (atSlot : frame.locals[id]? = some slot) : frame.getLocal id = .ok slot := by
  have bound : id < frame.locals.size := Array.getElem?_eq_some_iff.mp atSlot |>.1
  have value : frame.locals[id] = slot := Array.getElem?_eq_some_iff.mp atSlot |>.2
  simp [Frame.getLocal,bound,value,pure,Pure.pure,Except.pure]

 theorem get_operand (frame : F) (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout)
    (atSlot : frame.locals[id]? = some slot) (live : slot.value = .live (.immediate .uninit)) :
    frame.getLocalOperand id = .ok (.immediate .uninit) := by
  simp [Frame.getLocalOperand,get_local frame id slot atSlot,LocalState.access,live,
    Except.mapError,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

 theorem cached_at (frame : F) (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout)
    (layout : LocalLayout) (bound : id < frame.locals.size) :
    (cached frame id slot layout bound).locals[id]? = some {slot with layout := some layout} := by
  simp [cached]

 theorem cached_same (frame : F) (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout)
    (layout : LocalLayout) (bound : id < frame.locals.size)
    (atSlot : frame.locals[id]? = some slot) (layoutEq : slot.layout = some layout) :
    cached frame id slot layout bound = frame := by
  have value : frame.locals[id] = slot := Array.getElem?_eq_some_iff.mp atSlot |>.2
  have slotSame : {slot with layout := some layout} = slot := by rw [←layoutEq]
  unfold cached
  rw [slotSame,←value]
  simp only [Array.set_getElem_self]

 theorem local_layout (p : CompilerProviders.Prepared) (layout : LocalLayout)
    (frames : Array F) (frame : F) (machine : MachineHooks.MachineState K U) (id : MIR.LocalId)
    (normalized : CompilerFrameContext.normalizedLocalType p frame id = .ok layout.ty)
    (lookup : p.runtime.lookup layout.ty = .ok layout) :
    CompilerFrameContext.computeLocalLayout p id (LocalUnit.current frames frame machine) =
      .ok layout (LocalUnit.current frames frame machine) := by
  unfold CompilerFrameContext.computeLocalLayout
  simp [MachineHooks.currentFrame,LocalUnit.current,Stack.currentFrame?,normalized,lookup,Except.mapError,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
  simp_all!
  simp [pure,Pure.pure,EStateM.pure,lookup,Except.mapError]
  rfl

 theorem layout_cached (compiler : PlaceMachine.CompilerHooks K U C) (choice : C)
    (frames : Array F) (frame : F) (machine : MachineHooks.MachineState K U) (id : MIR.LocalId)
    (slot : LocalState Provenance LocalLayout) (layout : LocalLayout) (bound : id < frame.locals.size)
    (atSlot : frame.locals[id]? = some slot) (cache : slot.layout = none ∨ slot.layout = some layout)
    (computed : compiler.layout choice id (LocalUnit.current frames frame machine) =
      .ok layout (LocalUnit.current frames frame machine)) :
    PlaceMachine.layoutLocal compiler choice id (LocalUnit.current frames frame machine) =
      .ok layout (LocalUnit.current frames (cached frame id slot layout bound) machine) := by
  have got :=  get_local frame id slot atSlot
  have value : frame.locals[id] = slot := Array.getElem?_eq_some_iff.mp atSlot |>.2
  unfold PlaceMachine.layoutLocal
  simp only [MachineHooks.currentFrame,LocalUnit.current,Stack.currentFrame?,Array.back?_push,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,got]
  rcases cache with none | some
  · simp only [none,bind,Bind.bind,EStateM.bind]
    simp only [LocalUnit.current] at computed
    rw [computed]
    simp [Frame.getOrCacheLocalLayout,got,none,bound,value,cached,MachineHooks.currentFrame,
      MachineHooks.setCurrentFrame,LocalUnit.current,Stack.currentFrame?,
      get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
      set,MonadStateOf.set,EStateM.set,Except.pure,Except.bind]
  · rw [cached_same frame id slot layout bound atSlot some]
    simp [some,pure,Pure.pure,EStateM.pure]

 theorem read_cached [DecidableEq K] (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (frames : Array F) (frame : F) (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (layout : LocalLayout)
    (atSlot : frame.locals[id]? = some slot) (live : slot.value = .live (.immediate .uninit))
    (cache : slot.layout = some layout) (sized : layout.layout.isSized = true)
    (debugOff : compiler.debugAssertions = false) (noClocks : frame.extra.dataRace = none) :
    placeToOp (ValidityMachine.placeHooks access allocation compiler) choice
      ⟨.local frames.size id none frame.localsIdentity,layout⟩ (LocalUnit.current frames frame machine) =
      .ok ⟨.immediate .uninit,layout⟩ (LocalUnit.current frames frame machine) := by
  have got := get_local frame id slot atSlot
  have operand := get_operand frame id slot atSlot live
  cases ghost : machine.user.payload.ghost <;> with_unfolding_all
    simp [placeToOp,placeToOpCore,ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,
      PlaceMachine.placeHooks,PlaceMachine.localToOp,PlaceMachine.localToOpCore,PlaceMachine.layoutLocal,
      MachineHooks.currentFrame,LocalUnit.current,Stack.currentFrame?,Stack.frameIndex,got,cache,operand,
      sized,debugOff,ValidityMachine.validationInProgress,ghost,MachineHooks.afterLocalRead,noClocks,
      get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Except.pure,Except.bind,Except.mapError]

 theorem preflight [DecidableEq K] (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (frames : Array F) (frame : F) (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (layout : LocalLayout)
    (bound : id < frame.locals.size) (atSlot : frame.locals[id]? = some slot)
    (live : slot.value = .live (.immediate .uninit))
    (cache : slot.layout = none ∨ slot.layout = some layout) (sized : layout.layout.isSized = true)
    (computed : compiler.layout choice id (LocalUnit.current frames frame machine) =
      .ok layout (LocalUnit.current frames frame machine))
    (debugOff : compiler.debugAssertions = false) (noClocks : frame.extra.dataRace = none) :
    placeToOp (ValidityMachine.placeHooks access allocation compiler) choice
      ⟨.local frames.size id none frame.localsIdentity,layout⟩ (LocalUnit.current frames frame machine) =
      .ok ⟨.immediate .uninit,layout⟩
        (LocalUnit.current frames (cached frame id slot layout bound) machine) := by
  have lay := layout_cached (ValidityMachine.compilerPolicy compiler) choice frames frame machine id slot layout bound
    atSlot cache computed
  have operand := get_operand (cached frame id slot layout bound) id {slot with layout := some layout}
    (cached_at frame id slot layout bound) live
  have noClockCached : (cached frame id slot layout bound).extra.dataRace = none := noClocks
  have localRead : PlaceMachine.localToOp (ValidityMachine.compilerPolicy compiler) choice id
      (LocalUnit.current frames frame machine) =
      .ok ⟨.immediate .uninit,layout⟩ (LocalUnit.current frames (cached frame id slot layout bound) machine) := by
    unfold PlaceMachine.localToOp PlaceMachine.localToOpCore
    simp only [bind,Bind.bind,EStateM.bind]
    rw [lay]
    cases ghost : machine.user.payload.ghost <;> with_unfolding_all
      simp [MachineHooks.currentFrame,LocalUnit.current,Stack.currentFrame?,operand,sized,
        ValidityMachine.compilerPolicy,ValidityMachine.validationInProgress,ghost,MachineHooks.afterLocalRead,
        noClockCached,get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,
        EStateM.pure,Except.pure,Except.bind,Except.mapError]
  unfold placeToOp placeToOpCore
  simp [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,
    Stack.frameIndex,LocalUnit.current,debugOff,get,getThe,MonadStateOf.get,EStateM.get,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Except.pure,Except.bind]
  simp only [LocalUnit.current,ValidityMachine.compilerPolicy,debugOff] at localRead
  rw [localRead]

end EmptyFunction.LocalImmediate
