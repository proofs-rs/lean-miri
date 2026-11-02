import duplicate_prefix.AddFrameData
import duplicate_prefix.AddCallCore
import duplicate_prefix.AddLocalStages
import duplicate_prefix.AddArgument
import duplicate_prefix.PrimitiveArgumentCopy
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.AddInstall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts AddFrameData
noncomputable section

noncomputable def i1 : Fin 5 := ⟨1, by decide⟩
noncomputable def i2 : Fin 5 := ⟨2, by decide⟩
noncomputable def first (pointer : Scalar Provenance) : OpTy Provenance :=
  ⟨.immediate (.scalar pointer),
    CopyCompilerFacts.destPointerLayout⟩
noncomputable def second (n : UInt64) : OpTy Provenance :=
  ⟨.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 n))), RootCompilerFacts.usizeLayout⟩
noncomputable def firstCache (root : RootFrame) := cache (atSpan root ⟨616⟩) i1 CopyCompilerFacts.destPointerLayout
noncomputable def firstLive (root : RootFrame) := live (firstCache root) i1
noncomputable def firstDone (root : RootFrame) (pointer : Scalar Provenance) := write (firstLive root) i1
  (.scalar pointer)
noncomputable def secondCache (root : RootFrame) (pointer : Scalar Provenance) := cache (atSpan (firstDone root pointer) ⟨617⟩) i2 RootCompilerFacts.usizeLayout
noncomputable def secondLive (root : RootFrame) (pointer : Scalar Provenance) := live (secondCache root pointer) i2
noncomputable def result (root : RootFrame) (pointer : Scalar Provenance) (n : UInt64) := write (secondLive root pointer) i2
  (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 n)))

noncomputable def action (h : RootCallCore.RootHooks) (first second : OpTy Provenance) : MachineHooks.M MiriMemoryKind Machine.RootUser (Nat × Nat) := do
  AddCallCore.spanAt h (← h.localSpan HelperCompilerFacts.addBody.body 1)
  let ty ← h.localLayout () 1
  Call.passArgument h () (.Copy first) (HelperCompilerFacts.addAbi.args.getD 0 HelperCompilerFacts.addAbi.ret)
    (HelperCompilerFacts.addAbi.args.getD 0 HelperCompilerFacts.addAbi.ret) 0 ⟨1,#[]⟩ ty.ty false
  AddCallCore.spanAt h (← h.localSpan HelperCompilerFacts.addBody.body 2)
  let ty ← h.localLayout () 2
  Call.passArgument h () (.Copy second) (HelperCompilerFacts.addAbi.args.getD 1 HelperCompilerFacts.addAbi.ret)
    (HelperCompilerFacts.addAbi.args.getD 1 HelperCompilerFacts.addAbi.ret) 1 ⟨2,#[]⟩ ty.ty false
  pure (2,2)

theorem body (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (validityFuel : Nat)
    (validityEq : options.limits.validation = validityFuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra)) (root : RootFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Scalar Provenance) (n : UInt64)
    (dead1 : (root.frame.locals[1]'(root.valid i1)).value = .dead)
    (cache1 : (root.frame.locals[1]'(root.valid i1)).layout = none)
    (dead2 : (root.frame.locals[2]'(root.valid i2)).value = .dead)
    (cache2 : (root.frame.locals[2]'(root.valid i2)).layout = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow) :
    action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      (first pointer) (second n) (Storage.withCurrent frames root.frame machine) =
      .ok (2,2) (Storage.withCurrent frames (result root pointer n).frame (machine)) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let f1 := atSpan root ⟨616⟩
  let c1 := firstCache root
  let l1 := firstLive root
  let d1 := firstDone root pointer
  let m1 := machine
  let f2 := atSpan d1 ⟨617⟩
  let c2 := secondCache root pointer
  let l2 := secondLive root pointer
  let d2 := result root pointer n
  have span1 := AddLocalStages.span1 options limits (remaining+1) span frames root.frame machine root.body root.identity root.callee
  have get1 := CallEntryLocals.get_frame options limits (remaining+1) span frames root.frame machine
  have set1 := CallEntryLocals.set_frame options limits (remaining+1) span frames root.frame f1.frame machine
  have f1cache : (f1.frame.locals[1]'(f1.valid i1)).layout = none := cache1
  have layout1 := AddLocalStages.layout1 options limits (remaining+1) span frames f1.frame machine f1.body f1.identity f1.callee (f1.valid i1) f1cache
  have c1dead : (c1.frame.locals[1]'(c1.valid i1)).value = .dead := by
    simpa only [c1, firstCache, cache, LocalOperands.cachedLayoutFrame, Array.getElem_set_self, atSpan, i1, i2] using dead1
  have c1cache : (c1.frame.locals[1]'(c1.valid i1)).layout = some CopyCompilerFacts.destPointerLayout := by
    simp only [c1, firstCache, cache, LocalOperands.cachedLayoutFrame, Array.getElem_set_self, i1, i2]
  have l1live : (l1.frame.locals[1]'(l1.valid i1)).value = .live (.immediate .uninit) := by
    simp only [l1, firstLive, live, write, Array.getElem_set_self, i1, i2]
  have l1cache : (l1.frame.locals[1]'(l1.valid i1)).layout = some CopyCompilerFacts.destPointerLayout := by
    simpa only [l1, firstLive, live, write, Array.getElem_set_self, i1, i2] using c1cache
  have pass1 := AddArgument.pass_pointer options limits remaining span debug frames c1.frame machine pointer
    (c1.valid i1) c1.body c1cache c1dead c1.noClocks validityFuel validityEq ghost shallow
  change _ = (EStateM.Result.ok () (Storage.withCurrent frames d1.frame machine) : EStateM.Result StepError RootState Unit) at pass1
  have span2 := AddLocalStages.span2 options limits (remaining+1) span frames d1.frame m1 d1.body d1.identity d1.callee
  have get2 := CallEntryLocals.get_frame options limits (remaining+1) span frames d1.frame m1
  have set2 := CallEntryLocals.set_frame options limits (remaining+1) span frames d1.frame f2.frame m1
  have f2cache : (f2.frame.locals[2]'(f2.valid i2)).layout = none := by
    simpa [f2, d1, firstDone, firstLive, firstCache, atSpan, cache, live, write, LocalOperands.cachedLayoutFrame, i1, i2, root.size] using cache2
  have f2dead : (f2.frame.locals[2]'(f2.valid i2)).value = .dead := by
    simpa [f2, d1, firstDone, firstLive, firstCache, atSpan, cache, live, write, LocalOperands.cachedLayoutFrame, i1, i2, root.size] using dead2
  have layout2 := AddLocalStages.layout2 options limits (remaining+1) span frames f2.frame m1 f2.body f2.identity f2.callee (f2.valid i2) f2cache
  have c2dead : (c2.frame.locals[2]'(c2.valid i2)).value = .dead := by
    simpa only [c2, secondCache, cache, LocalOperands.cachedLayoutFrame, Array.getElem_set_self, i1, i2] using f2dead
  have c2cache : (c2.frame.locals[2]'(c2.valid i2)).layout = some RootCompilerFacts.usizeLayout := by
    simp only [c2, secondCache, cache, LocalOperands.cachedLayoutFrame, Array.getElem_set_self, i1, i2]
  have l2live : (l2.frame.locals[2]'(l2.valid i2)).value = .live (.immediate .uninit) := by
    simp only [l2, secondLive, live, write, Array.getElem_set_self, i1, i2]
  have l2cache : (l2.frame.locals[2]'(l2.valid i2)).layout = some RootCompilerFacts.usizeLayout := by
    simpa only [l2, secondLive, live, write, Array.getElem_set_self, i1, i2] using c2cache
  have pass2 := AddArgument.pass_usize options limits remaining span debug frames c2.frame machine n
    (c2.valid i2) c2.body c2cache c2dead c2.noClocks validityFuel validityEq ghost shallow
  change _ = (EStateM.Result.ok () (Storage.withCurrent frames d2.frame machine) : EStateM.Result StepError RootState Unit) at pass2
  change action h (first pointer) (second n) _ = _
  have ptrTy : CopyCompilerFacts.destPointerLayout.ty = 8 := by decide +kernel
  unfold action AddCallCore.spanAt
  simp only [bind, EStateM.bind]
  rw [span1]
  simp only [bind, EStateM.bind]
  rw [get1]
  simp only [bind, EStateM.bind]
  dsimp only [f1, atSpan] at set1
  rw [set1]
  simp only [bind, EStateM.bind]
  dsimp only [f1, atSpan] at layout1
  rw [layout1]
  simp only [bind, EStateM.bind, ptrTy]
  dsimp only [c1, firstCache, cache, atSpan] at pass1
  dsimp only [first]
  dsimp only [i1] at pass1 ⊢
  rw [pass1]
  simp only [bind, EStateM.bind]
  rw [span2]
  simp only [bind, EStateM.bind]
  rw [get2]
  simp only [bind, EStateM.bind]
  dsimp only [f2, atSpan] at set2
  rw [set2]
  simp only [bind, EStateM.bind]
  dsimp only [f2, atSpan] at layout2
  rw [layout2]
  simp only [bind, EStateM.bind]
  have usizeTy : RootCompilerFacts.usizeLayout.ty = 5 := by decide +kernel
  rw [usizeTy]
  dsimp only [c2, secondCache, cache, atSpan] at pass2
  dsimp only [second]
  dsimp only [i2] at pass2 ⊢
  rw [pass2]
  rfl

end
end DuplicatePrefix.AddInstall

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.AddInstall.body) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved empty root arguments dependency {dependency}"
