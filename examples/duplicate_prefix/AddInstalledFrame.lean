import duplicate_prefix.AddEntry
import duplicate_prefix.AddCallStep
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.AddInstalledFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Interpreter
open AddFrameData AddInstall
noncomputable def installed (root : RootFrame) (pointer : Scalar Provenance) (n : UInt64) (preamble callerSpan : SpanRef) :=
  AddDone.doneFrame {(AddInstall.result (AddTail.trackedRoot root callerSpan) pointer n).frame with location := .unwinding preamble}
 theorem metadata (root : RootFrame) (pointer : Scalar Provenance) (n : UInt64) (preamble callerSpan : SpanRef) :
    (installed root pointer n preamble callerSpan).body = root.frame.body ∧
    (installed root pointer n preamble callerSpan).bodyIdentity = root.frame.bodyIdentity ∧
    (installed root pointer n preamble callerSpan).functionInstance = root.frame.functionInstance ∧
    (installed root pointer n preamble callerSpan).returnContinuation = root.frame.returnContinuation ∧
    (installed root pointer n preamble callerSpan).returnPlace = root.frame.returnPlace ∧
    (installed root pointer n preamble callerSpan).vaList = root.frame.vaList ∧
    (installed root pointer n preamble callerSpan).extra.dataRace = root.frame.extra.dataRace ∧
    (installed root pointer n preamble callerSpan).extra.borrowTracker = root.frame.extra.borrowTracker ∧
    (installed root pointer n preamble callerSpan).location = .mir ⟨0,0⟩ := by
  simp only [installed, AddDone.doneFrame, CallEntryFacts.liveSlot, AddTail.trackedRoot, result, secondLive, secondCache, firstDone, firstLive, firstCache,
    live, write, cache, atSpan, LocalOperands.cachedLayoutFrame]
  repeat' constructor
 theorem size (root : RootFrame) (pointer : Scalar Provenance) (n : UInt64) (preamble callerSpan : SpanRef) :
    (installed root pointer n preamble callerSpan).locals.size = 5 := by
  simp only [installed, AddDone.doneFrame, CallEntryFacts.liveSlot, AddTail.trackedRoot, result, secondLive, secondCache, firstDone, firstLive, firstCache,
    live, write, cache, atSpan, LocalOperands.cachedLayoutFrame, Array.size_modify, Array.size_set, root.size]
 theorem slot (root : RootFrame) (raw : root.frame.locals = Array.replicate 5 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (pointer : Scalar Provenance) (n : UInt64) (preamble callerSpan : SpanRef) (i : Fin 5) :
    (installed root pointer n preamble callerSpan).locals[i.val]'(by rw [size]; exact i.isLt) =
    if 0 = i.val then ⟨.live (.immediate .uninit),none⟩
    else if 2 = i.val then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩
    else if 1 = i.val then ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.destPointerLayout⟩
    else ⟨.dead,none⟩ := by
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by omega
  rcases cases with h|h|h|h|h
  all_goals simp only [installed, AddDone.doneFrame, CallEntryFacts.liveSlot, AddTail.trackedRoot, result, secondLive, secondCache, firstDone, firstLive, firstCache,
    live, write, cache, atSpan, LocalOperands.cachedLayoutFrame, i1, i2,
    Array.getElem_modify, Array.getElem_set, Array.size_modify, Array.size_set, raw, Array.getElem_replicate,
    h, eq_self_iff_true, Nat.reduceEqDiff, ite_true, ite_false, or_true, true_or, false_or]
 theorem extra (root : RootFrame) (pointer : Scalar Provenance) (n : UInt64) (preamble callerSpan : SpanRef) :
    (installed root pointer n preamble callerSpan).extra = root.frame.extra := by
  simp only [installed, AddDone.doneFrame, CallEntryFacts.liveSlot, AddTail.trackedRoot, result, secondLive, secondCache, firstDone, firstLive, firstCache,
    live, write, cache, atSpan, LocalOperands.cachedLayoutFrame]
 theorem tracked_caller (root : RootFrame) (pointer : Scalar Provenance) (n : UInt64) (preamble callerSpan : SpanRef) :
    (installed root pointer n preamble callerSpan).trackCallerArg = some callerSpan := by
  simp only [installed, AddDone.doneFrame, CallEntryFacts.liveSlot, AddTail.trackedRoot, result, secondLive, secondCache, firstDone, firstLive, firstCache,
    live, write, cache, atSpan, LocalOperands.cachedLayoutFrame]
 theorem immediate (root : RootFrame) (raw : root.frame.locals = Array.replicate 5 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (pointer : Scalar Provenance) (n : UInt64) (preamble callerSpan : SpanRef) :
    ∀ current ∈ (installed root pointer n preamble callerSpan).locals, ∀ memory,
      current.value ≠ .live (.indirect memory) := by
  intro current member memory
  obtain ⟨index, valid, valueEq⟩ := Array.mem_iff_getElem.mp member
  have bounded : index < 5 := by rw [← size root pointer n preamble callerSpan]; exact valid
  rw [← valueEq, slot root raw pointer n preamble callerSpan ⟨index,bounded⟩]
  split
  · simp
  · by_cases h2 : (2:Nat) = index <;> by_cases h1 : (1:Nat) = index <;> simp [h2,h1]
end DuplicatePrefix.AddInstalledFrame
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.AddInstalledFrame." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved installed-frame dependency {dependency}"
