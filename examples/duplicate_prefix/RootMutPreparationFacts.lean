import duplicate_prefix.LocalDirectness
namespace DuplicatePrefix.RootMutPreparationFacts
open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- Pure local-frame preparation. The unit layout is an abstract parameter. -/
def result (frame : CompilerFrameContext.ActualFrame) (unitLayout : LocalLayout)
    (size : frame.locals.size = 25) : CompilerFrameContext.ActualFrame :=
  let f1 := SourceSteps.deadFrame frame ⟨6,0⟩ 10 (by rw [size];decide)
  let f2 := SourceSteps.deadFrame f1 ⟨6,1⟩ 9 (by simp [f1,SourceSteps.deadFrame,size])
  let v7 : (7 : Miri.MIR.LocalId) < f2.locals.size := by simp [f2,f1,SourceSteps.deadFrame,size]
  let f3 := {(ActualLocalCopy.written f2 7 unitLayout v7 .uninit) with location := .mir ⟨6,3⟩}
  let f4 := SourceSteps.deadFrame f3 ⟨6,3⟩ 8 (by simp [f3,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f2,f1,SourceSteps.deadFrame,size])
  let f5 := SourceSteps.deadFrame f4 ⟨6,4⟩ 7 (by simp [f4,SourceSteps.deadFrame,f3,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f2,f1,size])
  let f6 := SourceSteps.liveFrame f5 ⟨6,5⟩ 15 (by simp [f5,f4,f3,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f2,f1,size])
  SourceSteps.liveFrame f6 ⟨6,6⟩ 16 (by simp [f6,SourceSteps.liveFrame,f5,f4,f3,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f2,f1,size])

structure Shape (before after : CompilerFrameContext.ActualFrame) : Prop where
  body : after.body = before.body
  identity : after.bodyIdentity = before.bodyIdentity
  callee : after.functionInstance = before.functionInstance
  extra : after.extra = before.extra
  destination : after.returnPlace = before.returnPlace
  continuation : after.returnContinuation = before.returnContinuation
  varargs : after.vaList = before.vaList
  localsIdentity : after.localsIdentity = before.localsIdentity
  trackedCaller : after.trackCallerArg = before.trackCallerArg
  size : after.locals.size = 25
  location : after.location = .mir ⟨6,7⟩
  slot0 : after.locals[0]? = before.locals[0]?
  slot1 : after.locals[1]? = before.locals[1]?
  slot2 : after.locals[2]? = before.locals[2]?
  slot13 : after.locals[13]? = before.locals[13]?
  slot15 : after.locals[15]? = some ⟨.live (.immediate .uninit),none⟩
  slot16 : after.locals[16]? = some ⟨.live (.immediate .uninit),none⟩
  kept : ∀ id, id ≠ 7 → id ≠ 8 → id ≠ 9 → id ≠ 10 → id ≠ 15 → id ≠ 16 → after.locals[id]? = before.locals[id]?
  immediate : CopyHelperCleanup.AllImmediate before → CopyHelperCleanup.AllImmediate after

theorem shape (frame : CompilerFrameContext.ActualFrame) (unitLayout : LocalLayout)
    (size : frame.locals.size = 25)
    (none15 : (frame.locals[15]'(by omega)).layout = none)
    (none16 : (frame.locals[16]'(by omega)).layout = none) :
    Shape frame (result frame unitLayout size) := by
  constructor
  case immediate =>
    intro all
    unfold result
    apply LocalDirectness.live
    apply LocalDirectness.live
    apply LocalDirectness.dead
    apply LocalDirectness.dead
    apply LocalDirectness.written_at
    apply LocalDirectness.dead
    apply LocalDirectness.dead
    exact all
  case kept =>
    intro id not7 not8 not9 not10 not15 not16
    simp [result,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,
      Array.getElem?_set,Ne.symm not7,Ne.symm not8,Ne.symm not9,Ne.symm not10,Ne.symm not15,Ne.symm not16]
  all_goals simp [result,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,
    LocalPlaces.cachePlaceLayout,size,Array.getElem?_set,none15,none16]

#print axioms shape
end DuplicatePrefix.RootMutPreparationFacts
