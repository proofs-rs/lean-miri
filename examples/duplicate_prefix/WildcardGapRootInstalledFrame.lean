import duplicate_prefix.WildcardGapRootInvocationEntry
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.WildcardGapRootInstalledFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Interpreter
open RootFrameData WildcardGapRootArguments TypedBorrowSteps
noncomputable def installed (root : RootFrame) (target : TargetDataLayout) (address n : UInt64) (borrowFrame : FrameState) (id : AllocId) (child : BorTag) :=
  CallEntryFacts.doneRootFrame {registeredFrame {(result root target address n).frame with location := .unwinding ⟨601⟩}
    borrowFrame id child with location := .unwinding ⟨559⟩}
 theorem metadata (root : RootFrame) (target : TargetDataLayout) (address n : UInt64) (borrowFrame : FrameState) (id : AllocId) (child : BorTag) :
    (installed root target address n borrowFrame id child).body = root.frame.body ∧
    (installed root target address n borrowFrame id child).bodyIdentity = root.frame.bodyIdentity ∧
    (installed root target address n borrowFrame id child).functionInstance = root.frame.functionInstance ∧
    (installed root target address n borrowFrame id child).returnContinuation = root.frame.returnContinuation ∧
    (installed root target address n borrowFrame id child).returnPlace = root.frame.returnPlace ∧
    (installed root target address n borrowFrame id child).vaList = root.frame.vaList ∧
    (installed root target address n borrowFrame id child).extra.dataRace = root.frame.extra.dataRace ∧
    (installed root target address n borrowFrame id child).extra.borrowTracker = some (borrowFrame.addProtector id child) ∧
    (installed root target address n borrowFrame id child).location = .mir ⟨0,0⟩ := by
  simp only [installed, CallEntryFacts.doneRootFrame, CallEntryFacts.liveSlot, registeredFrame,
    TypedRetagEntry.frameWithBorrow, result, secondLive, secondCache, firstDone, firstLive, firstCache,
    live, write, cache, atSpan, LocalOperands.cachedLayoutFrame]
  repeat' constructor
 theorem size (root : RootFrame) (target : TargetDataLayout) (address n : UInt64) (borrowFrame : FrameState) (id : AllocId) (child : BorTag) :
    (installed root target address n borrowFrame id child).locals.size = 25 := by
  simp only [installed, CallEntryFacts.doneRootFrame, CallEntryFacts.liveSlot, registeredFrame,
    TypedRetagEntry.frameWithBorrow, result, secondLive, secondCache, firstDone, firstLive, firstCache,
    live, write, cache, atSpan, LocalOperands.cachedLayoutFrame, Array.size_modify, Array.size_set, root.size]
 theorem slot (root : RootFrame) (raw : root.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (target : TargetDataLayout) (address n : UInt64) (borrowFrame : FrameState) (id : AllocId) (child : BorTag) (i : Fin 25) :
    (installed root target address n borrowFrame id child).locals[i.val]'(by rw [size]; exact i.isLt) =
    if 14 = i.val ∨ 13 = i.val ∨ 6 = i.val ∨ 0 = i.val then ⟨.live (.immediate .uninit),none⟩
    else if 2 = i.val then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩
    else if 1 = i.val then ⟨.live (.immediate (RetagReferencePlace.sliceValue target (Pointer.new .wildcard (Size.ofBytes address)) 0 ActualReferenceMetadata.reference).imm),some ActualReferenceMetadata.reference⟩
    else ⟨.dead,none⟩ := by
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 ∨ i.val = 16 ∨ i.val = 17 ∨ i.val = 18 ∨ i.val = 19 ∨ i.val = 20 ∨ i.val = 21 ∨ i.val = 22 ∨ i.val = 23 ∨ i.val = 24 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp only [installed, CallEntryFacts.doneRootFrame, CallEntryFacts.liveSlot, registeredFrame,
    TypedRetagEntry.frameWithBorrow, result, secondLive, secondCache, firstDone, firstLive, firstCache,
    live, write, cache, atSpan, LocalOperands.cachedLayoutFrame, i1, i2,
    Array.getElem_modify, Array.getElem_set, Array.size_modify, Array.size_set, raw, Array.getElem_replicate,
    h, eq_self_iff_true, Nat.reduceEqDiff, ite_true, ite_false, or_true, true_or, false_or]
 theorem immediate (root : RootFrame) (raw : root.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (target : TargetDataLayout) (address n : UInt64) (borrowFrame : FrameState) (id : AllocId) (child : BorTag) :
    ∀ current ∈ (installed root target address n borrowFrame id child).locals, ∀ memory,
      current.value ≠ .live (.indirect memory) := by
  intro current member memory
  obtain ⟨index, valid, valueEq⟩ := Array.mem_iff_getElem.mp member
  have bounded : index < 25 := by rw [← size root target address n borrowFrame id child]; exact valid
  rw [← valueEq, slot root raw target address n borrowFrame id child ⟨index,bounded⟩]
  split
  · simp
  · by_cases h2 : (2:Nat) = index <;> by_cases h1 : (1:Nat) = index <;> simp [h2,h1]
 theorem empty_protectors (root : RootFrame) (target : TargetDataLayout) (address n : UInt64) (id : AllocId) (child : BorTag) :
    (installed root target address n {} id child).extra.borrowTracker = some ({protectedTags := #[(id,child)]} : FrameState) := by
  exact (metadata root target address n {} id child).2.2.2.2.2.2.2.1
end DuplicatePrefix.WildcardGapRootInstalledFrame
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.WildcardGapRootInstalledFrame." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved installed-frame dependency {dependency}"
