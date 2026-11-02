import duplicate_prefix.CopyEntryLocalStages
import duplicate_prefix.CopyFrameData
namespace DuplicatePrefix.CopyInstall
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts CopyFrameData
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable def argId (index : Fin 3) : Fin 17 := ⟨index.val+1,by have :=index.isLt;omega⟩
noncomputable def spanId (index : Fin 3) : Fin 4 := ⟨index.val+1,by have :=index.isLt;omega⟩
noncomputable def cached (root : RootFrame) (index : Fin 3) :=
  cache (atSpan root ⟨CopyEntrySpans.spanAt (spanId index)⟩) (argId index) (CopyArgumentStage.layout index)
noncomputable def completed (root : RootFrame) (index : Fin 3) (source destination : Scalar Provenance) (n : UInt64) :=
  write (live (cached root index) (argId index)) (argId index) (CopyArgumentStage.value source destination n index)
noncomputable def singleAction (h : CopyCallCore.RootHooks) (index : Fin 3)
    (source destination : Scalar Provenance) (n : UInt64) : MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  CopyCallCore.spanAt h (←h.localSpan HelperCompilerFacts.copyBody.body (index.val+1))
  let ty ← h.localLayout () (index.val+1)
  Call.passArgument h () (.Copy ⟨.immediate (CopyArgumentStage.value source destination n index),CopyArgumentStage.layout index⟩)
    (HelperCompilerFacts.copyAbi.args.getD index.val HelperCompilerFacts.copyAbi.ret)
    (HelperCompilerFacts.copyAbi.args.getD index.val HelperCompilerFacts.copyAbi.ret) index.val ⟨index.val+1,#[]⟩ ty.ty false
 theorem single (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (index : Fin 3) (source destination : Scalar Provenance) (n : UInt64)
    (dead : (root.frame.locals[index.val+1]'(root.valid (argId index))).value = .dead)
    (uncached : (root.frame.locals[index.val+1]'(root.valid (argId index))).layout = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow) :
    singleAction (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) index source destination n
      (Storage.withCurrent frames root.frame machine) =
      .ok () (Storage.withCurrent frames (completed root index source destination n).frame machine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  have query := CopyEntryLocalStages.local_span options limits (remaining+1) span frames root.frame machine root.body root.identity root.callee (spanId index)
  dsimp only [spanId] at query
  have setspan := CallEntryLocals.set_span options limits (remaining+1) span frames root.frame machine ⟨CopyEntrySpans.spanAt (spanId index)⟩
  change CopyCallCore.spanAt h ⟨CopyEntrySpans.spanAt (spanId index)⟩ (Storage.withCurrent frames root.frame machine) = _ at setspan
  dsimp only [h, spanId] at setspan
  let selected := atSpan root ⟨CopyEntrySpans.spanAt (spanId index)⟩
  have layout := CopyEntryLocalStages.argument_layout options limits (remaining+1) span frames selected.frame machine
    root.body root.identity root.callee index (root.valid (argId index)) uncached
  have valid : index.val+1 < (cached root index).frame.locals.size := (cached root index).valid (argId index)
  have cache : (cached root index).frame.locals[index.val+1].layout = some (CopyArgumentStage.layout index) := by
    simp [cached,CopyFrameData.cache,LocalOperands.cachedLayoutFrame,argId]
  have deadCache : (cached root index).frame.locals[index.val+1].value = .dead := by
    simpa only [cached,CopyFrameData.cache,CopyFrameData.atSpan,LocalOperands.cachedLayoutFrame,argId,Array.getElem_set_self] using dead
  have passed := CopyArgumentStage.pass_argument options limits remaining span debug frames (cached root index).frame machine
    index source destination n valid root.body cache deadCache root.noClocks fuel validationFuel ghost shallow
  unfold singleAction
  simp only [bind,EStateM.bind]
  rw [query]
  dsimp only
  rw [setspan]
  dsimp only [selected,atSpan,spanId] at layout
  dsimp only
  rw [layout]
  dsimp only
  dsimp only [cached,CopyFrameData.cache,CopyFrameData.atSpan,argId,spanId] at passed
  rw [passed]
  congr 1
noncomputable def first (source : Scalar Provenance) : OpTy Provenance := ⟨.immediate (.scalar source),CopyCompilerFacts.sourcePointerLayout⟩
noncomputable def second (destination : Scalar Provenance) : OpTy Provenance := ⟨.immediate (.scalar destination),CopyCompilerFacts.destPointerLayout⟩
noncomputable def third (n : UInt64) : OpTy Provenance := ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 n))),RootCompilerFacts.usizeLayout⟩
noncomputable def result (root : RootFrame) (source destination : Scalar Provenance) (n : UInt64) :=
  completed (completed (completed root 0 source destination n) 1 source destination n) 2 source destination n
noncomputable def action (h : CopyCallCore.RootHooks) (source destination : Scalar Provenance) (n : UInt64) := do
  singleAction h 0 source destination n
  singleAction h 1 source destination n
  singleAction h 2 source destination n
  pure (3,3)
theorem action_eq (h : CopyCallCore.RootHooks) (source destination : Scalar Provenance) (n : UInt64) :
    CopyCallCore.argumentBody h (first source) (second destination) (third n) = action h source destination n := by
  simp only [CopyCallCore.argumentBody,action,singleAction,first,second,third,CopyArgumentStage.value,CopyArgumentStage.layout]
  simp only [↓reduceIte,Fin.isValue,Fin.reduceEq,bind_assoc]
  rfl

theorem completed_other (root : RootFrame) (index : Fin 3) (other : Fin 17)
    (different : other.val ≠ index.val+1) (source destination : Scalar Provenance) (n : UInt64) :
    (completed root index source destination n).frame.locals[other.val]'((completed root index source destination n).valid other) = root.frame.locals[other.val]'(root.valid other) := by
  simp [completed,cached,CopyFrameData.write,CopyFrameData.live,CopyFrameData.cache,
    CopyFrameData.atSpan,LocalOperands.cachedLayoutFrame,argId,Array.getElem_set, Ne.symm different]

theorem body (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (source destination : Scalar Provenance) (n : UInt64)
    (dead : ∀ index : Fin 3, (root.frame.locals[index.val+1]'(root.valid (argId index))).value = .dead)
    (uncached : ∀ index : Fin 3, (root.frame.locals[index.val+1]'(root.valid (argId index))).layout = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow) :
    CopyCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      (first source) (second destination) (third n) (Storage.withCurrent frames root.frame machine) =
      .ok (3,3) (Storage.withCurrent frames (result root source destination n).frame machine) := by
  let stage1 := completed root 0 source destination n
  let stage2 := completed stage1 1 source destination n
  have other1 := completed_other root 0 (argId 1) (by decide) source destination n
  have other2 := completed_other root 0 (argId 2) (by decide) source destination n
  have other3 := completed_other stage1 1 (argId 2) (by decide) source destination n
  simp only [argId] at other1 other2 other3
  have dead1 : (stage1.frame.locals[(argId 1).val]'(stage1.valid (argId 1))).value = .dead := by dsimp only [stage1,argId]; rw [other1]; exact dead 1
  have cache1 : (stage1.frame.locals[(argId 1).val]'(stage1.valid (argId 1))).layout = none := by dsimp only [stage1,argId]; rw [other1]; exact uncached 1
  have dead2 : (stage2.frame.locals[(argId 2).val]'(stage2.valid (argId 2))).value = .dead := by dsimp only [stage2,argId]; rw [other3]; dsimp only [stage1]; rw [other2]; exact dead 2
  have cache2 : (stage2.frame.locals[(argId 2).val]'(stage2.valid (argId 2))).layout = none := by dsimp only [stage2,argId]; rw [other3]; dsimp only [stage1]; rw [other2]; exact uncached 2
  have firstStep := single options limits remaining span debug fuel validationFuel frames root machine 0 source destination n (dead 0) (uncached 0) ghost shallow
  have secondStep := single options limits remaining span debug fuel validationFuel frames stage1 machine 1 source destination n dead1 cache1 ghost shallow
  have thirdStep := single options limits remaining span debug fuel validationFuel frames stage2 machine 2 source destination n dead2 cache2 ghost shallow
  rw [action_eq]
  unfold action
  simp only [bind,EStateM.bind]
  rw [firstStep]
  dsimp only
  rw [secondStep]
  dsimp only
  rw [thirdStep]
  rfl

end
end DuplicatePrefix.CopyInstall
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.CopyInstall.single, ``DuplicatePrefix.CopyInstall.body] do
   for dependency in (←collectAxioms declaration) do
     unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
       throwError "unapproved copy argument install {dependency}"
