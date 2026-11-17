import duplicate_prefix.LocalDirectness
namespace DuplicatePrefix.RootSuccessCleanupFacts
open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

def result (frame : CompilerFrameContext.ActualFrame) (unitLayout boolLayout : LocalLayout)
    (value : Immediate Provenance) (size : frame.locals.size = 25) :=
  let f1 := SourceSteps.deadFrame frame ⟨9,0⟩ 24 (by rw [size];decide)
  let f2 := SourceSteps.deadFrame f1 ⟨9,1⟩ 21 (by simp [f1,SourceSteps.deadFrame,size])
  let f3 := SourceSteps.deadFrame f2 ⟨9,2⟩ 19 (by simp [f2,f1,SourceSteps.deadFrame,size])
  let f4 := SourceSteps.deadFrame f3 ⟨9,3⟩ 18 (by simp [f3,f2,f1,SourceSteps.deadFrame,size])
  let f5 := {(ActualLocalCopy.written f4 17 unitLayout (by simp [f4,f3,f2,f1,SourceSteps.deadFrame,size]) .uninit) with location := .mir ⟨9,5⟩}
  let f6 := SourceSteps.deadFrame f5 ⟨9,5⟩ 17 (by simp [f5,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f4,f3,f2,f1,SourceSteps.deadFrame,size])
  let f7 := {(ActualLocalCopy.written f6 0 boolLayout (by simp [f6,f5,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f4,f3,f2,f1,SourceSteps.deadFrame,size]) value) with location := .mir ⟨9,7⟩}
  SourceSteps.deadFrame f7 ⟨9,7⟩ 15 (by simp [f7,f6,f5,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f4,f3,f2,f1,SourceSteps.deadFrame,size])

structure Shape (before after : CompilerFrameContext.ActualFrame) (boolLayout : LocalLayout) (value : Immediate Provenance) : Prop where
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
  location : after.location = .mir ⟨9,8⟩
  kept : ∀ id, id ≠ 0 → id ≠ 15 → id ≠ 17 → id ≠ 18 → id ≠ 19 → id ≠ 21 → id ≠ 24 → after.locals[id]? = before.locals[id]?
  output : after.locals[0]? = some ⟨.live (.immediate value),some boolLayout⟩
  immediate : CopyHelperCleanup.AllImmediate before → CopyHelperCleanup.AllImmediate after

theorem shape (frame : CompilerFrameContext.ActualFrame) (unitLayout boolLayout : LocalLayout)
    (value : Immediate Provenance) (size : frame.locals.size = 25) :
    Shape frame (result frame unitLayout boolLayout value size) boolLayout value := by
  constructor
  case immediate =>
    intro all
    unfold result
    apply LocalDirectness.dead
    apply LocalDirectness.written_at
    apply LocalDirectness.dead
    apply LocalDirectness.written_at
    apply LocalDirectness.dead
    apply LocalDirectness.dead
    apply LocalDirectness.dead
    apply LocalDirectness.dead
    exact all
  case kept =>
    intro id not0 not15 not17 not18 not19 not21 not24
    simp [result,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,
      Array.getElem?_set,Ne.symm not0,Ne.symm not15,Ne.symm not17,Ne.symm not18,Ne.symm not19,Ne.symm not21,Ne.symm not24]
  all_goals simp [result,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,size]

#print axioms shape
end DuplicatePrefix.RootSuccessCleanupFacts
