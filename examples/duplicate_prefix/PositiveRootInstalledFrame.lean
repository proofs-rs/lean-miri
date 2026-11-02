import duplicate_prefix.PositiveRootInvocationEntry
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.PositiveRootInstalledFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Interpreter
open RootFrameData EmptyRootArguments TypedBorrowSteps PositiveRootArguments
noncomputable def installed (root : RootFrame) (adjusted : Immediate Provenance) (n : UInt64) (borrowFrame : FrameState) (buffer : AllocId) (bufferChild : BorTag) (id : AllocId) (child : BorTag) :=
  CallEntryFacts.doneRootFrame {registeredFrame {(RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted borrowFrame buffer bufferChild) n).frame with location := .unwinding ⟨601⟩}
    (borrowFrame.addProtector buffer bufferChild) id child with location := .unwinding ⟨559⟩}
 theorem metadata (root : RootFrame) (adjusted : Immediate Provenance) (n : UInt64) (borrowFrame : FrameState) (buffer : AllocId) (bufferChild : BorTag) (id : AllocId) (child : BorTag) :
    (installed root adjusted n borrowFrame buffer bufferChild id child).body = root.frame.body ∧
    (installed root adjusted n borrowFrame buffer bufferChild id child).bodyIdentity = root.frame.bodyIdentity ∧
    (installed root adjusted n borrowFrame buffer bufferChild id child).functionInstance = root.frame.functionInstance ∧
    (installed root adjusted n borrowFrame buffer bufferChild id child).returnContinuation = root.frame.returnContinuation ∧
    (installed root adjusted n borrowFrame buffer bufferChild id child).returnPlace = root.frame.returnPlace ∧
    (installed root adjusted n borrowFrame buffer bufferChild id child).vaList = root.frame.vaList ∧
    (installed root adjusted n borrowFrame buffer bufferChild id child).extra.dataRace = root.frame.extra.dataRace ∧
    (installed root adjusted n borrowFrame buffer bufferChild id child).extra.borrowTracker = some ((borrowFrame.addProtector buffer bufferChild).addProtector id child) ∧
    (installed root adjusted n borrowFrame buffer bufferChild id child).location = .mir ⟨0,0⟩ := by
  simp only [installed, CallEntryFacts.doneRootFrame, CallEntryFacts.liveSlot, registeredFrame,
    TypedRetagEntry.frameWithBorrow, RootArgumentsTwo.result, PositiveRootArguments.firstDone, protectedRoot, firstLive, firstCache,
    live, write, cache, atSpan, LocalOperands.cachedLayoutFrame]
  repeat' constructor
 theorem size (root : RootFrame) (adjusted : Immediate Provenance) (n : UInt64) (borrowFrame : FrameState) (buffer : AllocId) (bufferChild : BorTag) (id : AllocId) (child : BorTag) :
    (installed root adjusted n borrowFrame buffer bufferChild id child).locals.size = 25 := by
  simp only [installed, CallEntryFacts.doneRootFrame, CallEntryFacts.liveSlot, registeredFrame,
    TypedRetagEntry.frameWithBorrow, RootArgumentsTwo.result, PositiveRootArguments.firstDone, protectedRoot, firstLive, firstCache,
    live, write, cache, atSpan, LocalOperands.cachedLayoutFrame, Array.size_modify, Array.size_set, root.size]
 theorem slot_option (root : RootFrame) (raw : root.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (adjusted : Immediate Provenance) (n : UInt64) (borrowFrame : FrameState) (buffer : AllocId) (bufferChild : BorTag) (id : AllocId) (child : BorTag) (i : Fin 25) :
    (installed root adjusted n borrowFrame buffer bufferChild id child).locals[i.val]? = some (
    if 14 = i.val ∨ 13 = i.val ∨ 6 = i.val ∨ 0 = i.val then ⟨.live (.immediate .uninit),none⟩
    else if 2 = i.val then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩
    else if 1 = i.val then ⟨.live (.immediate adjusted),some ActualReferenceMetadata.reference⟩
    else ⟨.dead,none⟩) := by
  by_cases h0 : i.val = 0
  · simp only [installed, CallEntryFacts.doneRootFrame, CallEntryFacts.liveSlot, registeredFrame,
      TypedRetagEntry.frameWithBorrow, RootArgumentsTwo.result, PositiveRootArguments.firstDone, protectedRoot, firstLive, firstCache,
      live, write, cache, atSpan, LocalOperands.cachedLayoutFrame, i1, i2,
      Nat.reduceLT, Array.getElem_set_self, Array.getElem_set, Array.getElem_replicate, Array.getElem?_modify, Array.getElem?_set, Array.size_modify, Array.size_set, raw, Array.getElem?_replicate, i.isLt, Option.map_some,
      h0, eq_self_iff_true, Nat.reduceEqDiff, ite_true, ite_false, or_true, true_or, false_or]
  by_cases h1 : i.val = 1
  · simp only [installed, CallEntryFacts.doneRootFrame, CallEntryFacts.liveSlot, registeredFrame,
      TypedRetagEntry.frameWithBorrow, RootArgumentsTwo.result, PositiveRootArguments.firstDone, protectedRoot, firstLive, firstCache,
      live, write, cache, atSpan, LocalOperands.cachedLayoutFrame, i1, i2,
      Nat.reduceLT, Array.getElem_set_self, Array.getElem_set, Array.getElem_replicate, Array.getElem?_modify, Array.getElem?_set, Array.size_modify, Array.size_set, raw, Array.getElem?_replicate, i.isLt, Option.map_some,
      h1, eq_self_iff_true, Nat.reduceEqDiff, ite_true, ite_false, or_true, true_or, false_or]
  by_cases h2 : i.val = 2
  · simp only [installed, CallEntryFacts.doneRootFrame, CallEntryFacts.liveSlot, registeredFrame,
      TypedRetagEntry.frameWithBorrow, RootArgumentsTwo.result, PositiveRootArguments.firstDone, protectedRoot, firstLive, firstCache,
      live, write, cache, atSpan, LocalOperands.cachedLayoutFrame, i1, i2,
      Nat.reduceLT, Array.getElem_set_self, Array.getElem_set, Array.getElem_replicate, Array.getElem?_modify, Array.getElem?_set, Array.size_modify, Array.size_set, raw, Array.getElem?_replicate, i.isLt, Option.map_some,
      h2, eq_self_iff_true, Nat.reduceEqDiff, ite_true, ite_false, or_true, true_or, false_or]
  by_cases h6 : i.val = 6
  · simp only [installed, CallEntryFacts.doneRootFrame, CallEntryFacts.liveSlot, registeredFrame,
      TypedRetagEntry.frameWithBorrow, RootArgumentsTwo.result, PositiveRootArguments.firstDone, protectedRoot, firstLive, firstCache,
      live, write, cache, atSpan, LocalOperands.cachedLayoutFrame, i1, i2,
      Nat.reduceLT, Array.getElem_set_self, Array.getElem_set, Array.getElem_replicate, Array.getElem?_modify, Array.getElem?_set, Array.size_modify, Array.size_set, raw, Array.getElem?_replicate, i.isLt, Option.map_some,
      h6, eq_self_iff_true, Nat.reduceEqDiff, ite_true, ite_false, or_true, true_or, false_or]
  by_cases h13 : i.val = 13
  · simp only [installed, CallEntryFacts.doneRootFrame, CallEntryFacts.liveSlot, registeredFrame,
      TypedRetagEntry.frameWithBorrow, RootArgumentsTwo.result, PositiveRootArguments.firstDone, protectedRoot, firstLive, firstCache,
      live, write, cache, atSpan, LocalOperands.cachedLayoutFrame, i1, i2,
      Nat.reduceLT, Array.getElem_set_self, Array.getElem_set, Array.getElem_replicate, Array.getElem?_modify, Array.getElem?_set, Array.size_modify, Array.size_set, raw, Array.getElem?_replicate, i.isLt, Option.map_some,
      h13, eq_self_iff_true, Nat.reduceEqDiff, ite_true, ite_false, or_true, true_or, false_or]
  by_cases h14 : i.val = 14
  · simp only [installed, CallEntryFacts.doneRootFrame, CallEntryFacts.liveSlot, registeredFrame,
      TypedRetagEntry.frameWithBorrow, RootArgumentsTwo.result, PositiveRootArguments.firstDone, protectedRoot, firstLive, firstCache,
      live, write, cache, atSpan, LocalOperands.cachedLayoutFrame, i1, i2,
      Nat.reduceLT, Array.getElem_set_self, Array.getElem_set, Array.getElem_replicate, Array.getElem?_modify, Array.getElem?_set, Array.size_modify, Array.size_set, raw, Array.getElem?_replicate, i.isLt, Option.map_some,
      h14, eq_self_iff_true, Nat.reduceEqDiff, ite_true, ite_false, or_true, true_or, false_or]
  simp only [installed, CallEntryFacts.doneRootFrame, CallEntryFacts.liveSlot, registeredFrame,
    TypedRetagEntry.frameWithBorrow, RootArgumentsTwo.result, PositiveRootArguments.firstDone, protectedRoot, firstLive, firstCache,
    live, write, cache, atSpan, LocalOperands.cachedLayoutFrame, i1, i2,
    Nat.reduceLT, Array.getElem_set_self, Array.getElem_set, Array.getElem_replicate, Array.getElem?_modify, Array.getElem?_set, Array.size_modify, Array.size_set, raw, Array.getElem?_replicate, i.isLt, Option.map_some,
    h0,Ne.symm h0,h1,Ne.symm h1,h2,Ne.symm h2,h6,Ne.symm h6,h13,Ne.symm h13,h14,Ne.symm h14, eq_self_iff_true, Nat.reduceEqDiff, ite_true, ite_false, or_true, true_or, false_or]

 theorem slot (root : RootFrame) (raw : root.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (adjusted : Immediate Provenance) (n : UInt64) (borrowFrame : FrameState) (buffer : AllocId) (bufferChild : BorTag) (id : AllocId) (child : BorTag) (i : Fin 25) :
    (installed root adjusted n borrowFrame buffer bufferChild id child).locals[i.val]'(by rw [size]; exact i.isLt) =
    if 14 = i.val ∨ 13 = i.val ∨ 6 = i.val ∨ 0 = i.val then ⟨.live (.immediate .uninit),none⟩
    else if 2 = i.val then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩
    else if 1 = i.val then ⟨.live (.immediate adjusted),some ActualReferenceMetadata.reference⟩
    else ⟨.dead,none⟩ := by
  have known := slot_option root raw adjusted n borrowFrame buffer bufferChild id child i
  exact Option.some.inj ((Array.getElem?_eq_getElem (by rw [size];exact i.isLt)).symm.trans known)
 theorem immediate (root : RootFrame) (raw : root.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (adjusted : Immediate Provenance) (n : UInt64) (borrowFrame : FrameState) (buffer : AllocId) (bufferChild : BorTag) (id : AllocId) (child : BorTag) :
    ∀ current ∈ (installed root adjusted n borrowFrame buffer bufferChild id child).locals, ∀ memory,
      current.value ≠ .live (.indirect memory) := by
  intro current member memory
  obtain ⟨index, valid, valueEq⟩ := Array.mem_iff_getElem.mp member
  have bounded : index < 25 := by rw [← size root adjusted n borrowFrame buffer bufferChild id child]; exact valid
  rw [← valueEq, slot root raw adjusted n borrowFrame buffer bufferChild id child ⟨index,bounded⟩]
  split
  · simp
  · by_cases h2 : (2:Nat) = index <;> by_cases h1 : (1:Nat) = index <;> simp [h2,h1]
 theorem two_protectors (root : RootFrame) (adjusted : Immediate Provenance) (n : UInt64)
    (buffer id : AllocId) (bufferChild child : BorTag) :
    (installed root adjusted n {} buffer bufferChild id child).extra.borrowTracker =
      some ({protectedTags := #[(buffer,bufferChild),(id,child)]} : FrameState) := by
  exact (metadata root adjusted n {} buffer bufferChild id child).2.2.2.2.2.2.2.1
 theorem track (root : RootFrame) (adjusted : Immediate Provenance) (n : UInt64) (borrowFrame : FrameState)
    (buffer : AllocId) (bufferChild : BorTag) (id : AllocId) (child : BorTag) :
    (installed root adjusted n borrowFrame buffer bufferChild id child).trackCallerArg = root.frame.trackCallerArg := by
  simp only [installed, CallEntryFacts.doneRootFrame, CallEntryFacts.liveSlot, registeredFrame,
    TypedRetagEntry.frameWithBorrow, RootArgumentsTwo.result, PositiveRootArguments.firstDone, protectedRoot, firstLive, firstCache,
    live, write, cache, atSpan, LocalOperands.cachedLayoutFrame]
 theorem relevance (root : RootFrame) (adjusted : Immediate Provenance) (n : UInt64) (borrowFrame : FrameState)
    (buffer : AllocId) (bufferChild : BorTag) (id : AllocId) (child : BorTag) :
    (installed root adjusted n borrowFrame buffer bufferChild id child).extra.userRelevance = root.frame.extra.userRelevance := by
  simp only [installed, CallEntryFacts.doneRootFrame, CallEntryFacts.liveSlot, registeredFrame,
    TypedRetagEntry.frameWithBorrow, RootArgumentsTwo.result, PositiveRootArguments.firstDone, protectedRoot, firstLive, firstCache,
    live, write, cache, atSpan, LocalOperands.cachedLayoutFrame]
 theorem raw_relevance (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (place : MPlaceTy Provenance)
    (race : before.dataRace = none) : (RawRootInvocation.root before place race).frame.extra.userRelevance = 255 := by
  simp only [RawRootInvocation.root, RootFrameData.raw, CallEntryFacts.rawRootFrame]
end DuplicatePrefix.PositiveRootInstalledFrame
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.PositiveRootInstalledFrame." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved positive installed-frame dependency {dependency}"
