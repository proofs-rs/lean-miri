import duplicate_prefix.ReferenceBorrowDriver
import duplicate_prefix.RootFrameData
import duplicate_prefix.RootCallCore
import duplicate_prefix.WildcardOrderedMissArgumentCopy
import duplicate_prefix.PrimitiveArgumentCopy
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.WildcardOrderedMissRootArguments
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts RootFrameData
noncomputable section

noncomputable def i1 : Fin 25 := ⟨1, by decide⟩
noncomputable def i2 : Fin 25 := ⟨2, by decide⟩
noncomputable def first (target : TargetDataLayout) (address : UInt64) : OpTy Provenance :=
  ⟨.immediate (RetagReferencePlace.sliceValue target (Pointer.new .wildcard (Size.ofBytes address)) 0 ActualReferenceMetadata.reference).imm,
    ActualReferenceMetadata.reference⟩
noncomputable def second (n : UInt64) : OpTy Provenance :=
  ⟨.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 n))), RootCompilerFacts.usizeLayout⟩
noncomputable def firstCache (root : RootFrame) := cache (atSpan root ⟨602⟩) i1 ActualReferenceMetadata.reference
noncomputable def firstLive (root : RootFrame) := live (firstCache root) i1
noncomputable def firstDone (root : RootFrame) (target : TargetDataLayout) (address : UInt64) := write (firstLive root) i1
  (RetagReferencePlace.sliceValue target (Pointer.new .wildcard (Size.ofBytes address)) 0 ActualReferenceMetadata.reference).imm
noncomputable def secondCache (root : RootFrame) (target : TargetDataLayout) (address : UInt64) := cache (atSpan (firstDone root target address) ⟨603⟩) i2 RootCompilerFacts.usizeLayout
noncomputable def secondLive (root : RootFrame) (target : TargetDataLayout) (address : UInt64) := live (secondCache root target address) i2
noncomputable def result (root : RootFrame) (target : TargetDataLayout) (address n : UInt64) := write (secondLive root target address) i2
  (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 n)))

theorem body (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (debug : options.place.debugAssertions = false) (dynamicFuel validityFuel : Nat)
    (dynamicEq : options.place.dynamicFuel = dynamicFuel + 1)
    (validityEq : options.limits.validation = validityFuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra)) (root : RootFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (target : TargetDataLayout)
    (targetEq : target = (ActualReferenceContext.config options remaining span).access.runtime.base)
    (address n : UInt64) (nonzero : address ≠ 0)
    (dead1 : (root.frame.locals[1]'(root.valid i1)).value = .dead)
    (cache1 : (root.frame.locals[1]'(root.valid i1)).layout = none)
    (dead2 : (root.frame.locals[2]'(root.valid i2)).value = .dead)
    (cache2 : (root.frame.locals[2]'(root.valid i2)).layout = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (miss : WildcardOrderedMissAddress.Miss machine.user.addresses address)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false) :
    RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      (first target address) (second n) (Storage.withCurrent frames root.frame machine) =
      .ok (2,2) (Storage.withCurrent frames (result root target address n).frame (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let f1 := atSpan root ⟨602⟩
  let c1 := firstCache root
  let l1 := firstLive root
  let d1 := firstDone root target address
  let m1 := ReferenceBorrowDriver.allocatedMachine machine tracker fresh
  let f2 := atSpan d1 ⟨603⟩
  let c2 := secondCache root target address
  let l2 := secondLive root target address
  let d2 := result root target address n
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
  have copy1 := WildcardOrderedMissArgumentCopy.copy_empty_argument options limits remaining span cmp precise implicitWrites debug
    dynamicFuel validityFuel dynamicEq validityEq frames l1.frame machine 1 .uninit (l1.valid i1) l1live l1cache l1.noClocks
    ghost shallow address nonzero tracker enabled mode fresh addressMode miss metadata notConstructed
    (LocalPlaces.localRuntimePlace frames.size l1.frame 1 ActualReferenceMetadata.reference).stackView (by simp)
  rw [←targetEq] at copy1
  have pass1 := RootArgumentEntry.pass1_of_copy options limits (remaining+1) span debug frames c1.frame machine
    (RetagReferencePlace.sliceValue target (Pointer.new .wildcard (Size.ofBytes address)) 0 ActualReferenceMetadata.reference).imm (c1.valid i1) c1.body c1cache c1dead c1.noClocks
    (Storage.withCurrent frames d1.frame m1) copy1
  have span2 := CallEntryLocals.root_span2 options limits (remaining+1) span frames d1.frame m1 d1.body d1.identity d1.callee
  have get2 := CallEntryLocals.get_frame options limits (remaining+1) span frames d1.frame m1
  have set2 := CallEntryLocals.set_frame options limits (remaining+1) span frames d1.frame f2.frame m1
  have f2cache : (f2.frame.locals[2]'(f2.valid i2)).layout = none := by
    simpa [f2, d1, firstDone, firstLive, firstCache, atSpan, cache, live, write, LocalOperands.cachedLayoutFrame, i1, i2, root.size] using cache2
  have f2dead : (f2.frame.locals[2]'(f2.valid i2)).value = .dead := by
    simpa [f2, d1, firstDone, firstLive, firstCache, atSpan, cache, live, write, LocalOperands.cachedLayoutFrame, i1, i2, root.size] using dead2
  have layout2 := CallEntryLocals.root_layout2 options limits (remaining+1) span frames f2.frame m1 f2.body f2.identity f2.callee (f2.valid i2) f2cache
  have c2dead : (c2.frame.locals[2]'(c2.valid i2)).value = .dead := by
    simpa only [c2, secondCache, cache, LocalOperands.cachedLayoutFrame, Array.getElem_set_self, i1, i2] using f2dead
  have c2cache : (c2.frame.locals[2]'(c2.valid i2)).layout = some RootCompilerFacts.usizeLayout := by
    simp only [c2, secondCache, cache, LocalOperands.cachedLayoutFrame, Array.getElem_set_self, i1, i2]
  have l2live : (l2.frame.locals[2]'(l2.valid i2)).value = .live (.immediate .uninit) := by
    simp only [l2, secondLive, live, write, Array.getElem_set_self, i1, i2]
  have l2cache : (l2.frame.locals[2]'(l2.valid i2)).layout = some RootCompilerFacts.usizeLayout := by
    simpa only [l2, secondLive, live, write, Array.getElem_set_self, i1, i2] using c2cache
  have copy2 := PrimitiveArgumentCopy.copy_usize_argument options limits remaining span debug validityFuel validityEq
    frames l2.frame m1 2 .uninit n (l2.valid i2) l2live l2cache l2.noClocks ghost shallow
    (LocalPlaces.localRuntimePlace frames.size l2.frame 2 RootCompilerFacts.usizeLayout).stackView (by simp)
  have pass2 := RootArgumentEntry.pass2_of_copy options limits (remaining+1) span debug frames c2.frame m1
    (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 n))) (c2.valid i2) c2.body c2cache c2dead c2.noClocks
    (Storage.withCurrent frames d2.frame m1) copy2
  change RootCallCore.argumentBody h (first target address) (second n) _ = _
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
  dsimp only [first]
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
  dsimp only [c2, secondCache, cache, atSpan] at pass2
  dsimp only [second]
  dsimp only [i2] at pass2 ⊢
  rw [pass2]
  rfl

end
end DuplicatePrefix.WildcardOrderedMissRootArguments
