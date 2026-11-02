import duplicate_prefix.EmptyRootArguments
namespace DuplicatePrefix.RootArgumentsTwo
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts RootFrameData EmptyRootArguments
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
noncomputable def result (firstDone : RootFrame) (n : UInt64) :=
  write (live (cache (atSpan firstDone ⟨603⟩) i2 RootCompilerFacts.usizeLayout) i2) i2
    (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 n)))

theorem body (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (validityFuel : Nat)
    (validityEq : options.limits.validation = validityFuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (root d1 : RootFrame)
    (machine m1 : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (value : Immediate Provenance) (n : UInt64)
    (dead1 : (root.frame.locals[1]'(root.valid i1)).value = .dead)
    (cache1 : (root.frame.locals[1]'(root.valid i1)).layout = none)
    (nextDead : (d1.frame.locals[2]'(d1.valid i2)).value = .dead)
    (nextCache : (d1.frame.locals[2]'(d1.valid i2)).layout = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (nextGhost : m1.user.payload.ghost = false) (nextShallow : m1.user.payload.validation = .Shallow)
    (copy1 : (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace frames.size (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames (firstLive root).frame machine) =
      .ok () (Storage.withCurrent frames d1.frame m1)) :
    RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second n) (Storage.withCurrent frames root.frame machine) =
      .ok (2,2) (Storage.withCurrent frames (result d1 n).frame m1) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let f1 := atSpan root ⟨602⟩
  let c1 := firstCache root
  let l1 := firstLive root
  let f2 := atSpan d1 ⟨603⟩
  let c2 := cache f2 i2 RootCompilerFacts.usizeLayout
  let l2 := live c2 i2
  let d2 := result d1 n
  have span1 := CallEntryLocals.root_span1 options limits (remaining+1) span frames root.frame machine root.body root.identity root.callee
  have get1 := CallEntryLocals.get_frame options limits (remaining+1) span frames root.frame machine
  have set1 := CallEntryLocals.set_frame options limits (remaining+1) span frames root.frame f1.frame machine
  have f1cache : (f1.frame.locals[1]'(f1.valid i1)).layout = none := cache1
  have layout1 := CallEntryLocals.root_layout1 options limits (remaining+1) span frames f1.frame machine f1.body f1.identity f1.callee (f1.valid i1) f1cache
  have c1dead : (c1.frame.locals[1]'(c1.valid i1)).value = .dead := by
    simpa only [c1, firstCache, cache, LocalOperands.cachedLayoutFrame, Array.getElem_set_self, atSpan, i1, i2] using dead1
  have c1cache : (c1.frame.locals[1]'(c1.valid i1)).layout = some ActualReferenceMetadata.reference := by
    simp only [c1, firstCache, cache, LocalOperands.cachedLayoutFrame, Array.getElem_set_self, i1, i2]
  have l1live : (l1.frame.locals[1]'(l1.valid i1)).value = .live (.immediate .uninit) := by
    simp only [l1, firstLive, live, write, Array.getElem_set_self, i1, i2]
  have l1cache : (l1.frame.locals[1]'(l1.valid i1)).layout = some ActualReferenceMetadata.reference := by
    simpa only [l1, firstLive, live, write, Array.getElem_set_self, i1, i2] using c1cache
  have pass1 := RootArgumentEntry.pass1_of_copy options limits (remaining+1) span debug frames c1.frame machine
    value (c1.valid i1) c1.body c1cache c1dead c1.noClocks
    (Storage.withCurrent frames d1.frame m1) copy1
  have span2 := CallEntryLocals.root_span2 options limits (remaining+1) span frames d1.frame m1 d1.body d1.identity d1.callee
  have get2 := CallEntryLocals.get_frame options limits (remaining+1) span frames d1.frame m1
  have set2 := CallEntryLocals.set_frame options limits (remaining+1) span frames d1.frame f2.frame m1
  have f2cache : (f2.frame.locals[2]'(f2.valid i2)).layout = none := nextCache
  have f2dead : (f2.frame.locals[2]'(f2.valid i2)).value = .dead := nextDead
  have layout2 := CallEntryLocals.root_layout2 options limits (remaining+1) span frames f2.frame m1 f2.body f2.identity f2.callee (f2.valid i2) f2cache
  have c2dead : (c2.frame.locals[2]'(c2.valid i2)).value = .dead := by
    simpa only [c2, cache, LocalOperands.cachedLayoutFrame, Array.getElem_set_self, i1, i2] using f2dead
  have c2cache : (c2.frame.locals[2]'(c2.valid i2)).layout = some RootCompilerFacts.usizeLayout := by
    simp only [c2, cache, LocalOperands.cachedLayoutFrame, Array.getElem_set_self, i1, i2]
  have l2live : (l2.frame.locals[2]'(l2.valid i2)).value = .live (.immediate .uninit) := by
    simp only [l2, live, write, Array.getElem_set_self, i1, i2]
  have l2cache : (l2.frame.locals[2]'(l2.valid i2)).layout = some RootCompilerFacts.usizeLayout := by
    simpa only [l2, live, write, Array.getElem_set_self, i1, i2] using c2cache
  have copy2 := PrimitiveArgumentCopy.copy_usize_argument options limits remaining span debug validityFuel validityEq
    frames l2.frame m1 2 .uninit n (l2.valid i2) l2live l2cache l2.noClocks nextGhost nextShallow
    (LocalPlaces.localRuntimePlace frames.size l2.frame 2 RootCompilerFacts.usizeLayout).stackView (by simp)
  have pass2 := RootArgumentEntry.pass2_of_copy options limits (remaining+1) span debug frames c2.frame m1
    (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 n))) (c2.valid i2) c2.body c2cache c2dead c2.noClocks
    (Storage.withCurrent frames d2.frame m1) copy2
  change RootCallCore.argumentBody h ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second n) _ = _
  unfold RootCallCore.argumentBody RootCallCore.spanAt
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
  simp only [bind, EStateM.bind, ActualReferenceMetadata.reference_ty]
  dsimp only [c1, firstCache, cache, atSpan] at pass1
  dsimp only [ActualReferenceMetadata.reference, i1] at pass1 ⊢
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
  dsimp only [c2, cache, f2, atSpan] at pass2
  dsimp only [EmptyRootArguments.second]
  dsimp only [i2] at pass2 ⊢
  rw [pass2]
  rfl

end
end DuplicatePrefix.RootArgumentsTwo
