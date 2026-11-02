import duplicate_prefix.CopyHelperSteps
namespace DuplicatePrefix.CopyHelperCleanup
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def AllImmediate (frame : CompilerFrameContext.ActualFrame) : Prop :=
  ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory)

theorem all_immediate_set (frame : CompilerFrameContext.ActualFrame) (id : MIR.LocalId)
    (slot : LocalState Provenance LocalLayout) (valid : id < frame.locals.size)
    (all : AllImmediate frame) (immediate : ∀ memory, slot.value ≠ .live (.indirect memory)) :
    AllImmediate {frame with locals := frame.locals.set id slot valid} := by
  intro entry member memory
  rcases Array.mem_or_eq_of_mem_set (w := valid) member with old | rfl
  · exact all entry old memory
  · exact immediate memory

theorem all_immediate_cache (frame : CompilerFrameContext.ActualFrame) (id : MIR.LocalId)
    (layout : LocalLayout) (valid : id < frame.locals.size) (all : AllImmediate frame) :
    AllImmediate (LocalPlaces.cachePlaceLayout frame id layout valid) := by
  apply all_immediate_set frame id _ valid all
  intro memory
  exact all frame.locals[id] (Array.mem_iff_getElem.mpr ⟨id,valid,rfl⟩) memory

theorem all_immediate_written (frame : CompilerFrameContext.ActualFrame) (id : MIR.LocalId)
    (layout : LocalLayout) (value : Immediate Provenance) (valid : id < frame.locals.size)
    (all : AllImmediate frame) :
    AllImmediate (ActualLocalCopy.written frame id layout valid value) := by
  apply all_immediate_set (LocalPlaces.cachePlaceLayout frame id layout valid) id _ _
    (all_immediate_cache frame id layout valid all)
  intro memory
  simp

theorem actual_three_dead
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (source dest : Scalar Provenance) (n : UInt64)
    (size : frame.locals.size = 17)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (location : frame.location = .mir ⟨7,9⟩)
    (live14 : (frame.locals[14]'(by omega)).value = .live (.immediate (.scalar source)))
    (live15 : (frame.locals[15]'(by omega)).value = .live (.immediate (.scalar dest)))
    (live16 : (frame.locals[16]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (all : AllImmediate frame) :
    let config := PreparedContracts.actualConfig options () remaining span
    ∃ f1 f2 done : CompilerFrameContext.ActualFrame,
      ExecutionMachine.step config limits () (Storage.withCurrent frames frame machine) =
        (Storage.withCurrent frames f1 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent frames f1 machine) =
        (Storage.withCurrent frames f2 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent frames f2 machine) =
        (Storage.withCurrent frames done machine,.ok true) ∧
      done.body = frame.body ∧ done.bodyIdentity = frame.bodyIdentity ∧ done.functionInstance = frame.functionInstance ∧
      done.extra = frame.extra ∧ done.returnPlace = frame.returnPlace ∧ done.returnContinuation = frame.returnContinuation ∧
      done.vaList = frame.vaList ∧ done.localsIdentity = frame.localsIdentity ∧ done.locals.size = 17 ∧
      done.location = .mir ⟨7,12⟩ ∧ done.locals[0]? = frame.locals[0]? ∧ AllImmediate done := by
  let config := PreparedContracts.actualConfig options () remaining span
  have v14 : (14 : MIR.LocalId) < frame.locals.size := by rw [size];decide
  have v15 : (15 : MIR.LocalId) < frame.locals.size := by rw [size];decide
  have v16 : (16 : MIR.LocalId) < frame.locals.size := by rw [size];decide
  let f1 := SourceSteps.deadFrame frame ⟨7,9⟩ 16 v16
  have v15f1 : (15 : MIR.LocalId) < f1.locals.size := by simpa [f1,SourceSteps.deadFrame] using v15
  let f2 := SourceSteps.deadFrame f1 ⟨7,10⟩ 15 v15f1
  have v14f2 : (14 : MIR.LocalId) < f2.locals.size := by simpa [f2,f1,SourceSteps.deadFrame] using v14
  let done := SourceSteps.deadFrame f2 ⟨7,11⟩ 14 v14f2
  have first := CopyHelperSteps.storage_dead options limits remaining span frames frame machine
    ⟨7,9⟩ 16 (.scalar (.fromScalarInt (.ofUInt64 n))) sourceBody location (by decide +kernel) (by decide) v16 live16
  have second := CopyHelperSteps.storage_dead options limits remaining span frames f1 machine
    ⟨7,10⟩ 15 (.scalar dest) sourceBody rfl (by decide +kernel) (by decide) v15f1
    (by simpa [f1,SourceSteps.deadFrame,Array.getElem_set] using live15)
  have third := CopyHelperSteps.storage_dead options limits remaining span frames f2 machine
    ⟨7,11⟩ 14 (.scalar source) sourceBody rfl (by decide +kernel) (by decide) v14f2
    (by simpa [f2,f1,SourceSteps.deadFrame,Array.getElem_set] using live14)
  have all1 : AllImmediate f1 := all_immediate_set frame 16 _ v16 all (by intro memory; simp)
  have all2 : AllImmediate f2 := all_immediate_set f1 15 _ v15f1 all1 (by intro memory; simp)
  have allDone : AllImmediate done := all_immediate_set f2 14 _ v14f2 all2 (by intro memory; simp)
  refine ⟨f1,f2,done,first,second,third,?_⟩
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,rfl,?_,allDone⟩
  · simpa [done,f2,f1,SourceSteps.deadFrame] using size
  · simp [done,f2,f1,SourceSteps.deadFrame,Array.getElem?_set]

#print axioms actual_three_dead
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``actual_three_dead) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved axiom {dependency}"
end DuplicatePrefix.CopyHelperCleanup
