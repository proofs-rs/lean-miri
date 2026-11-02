import duplicate_prefix.CurrentCallResourceEntry
import duplicate_prefix.CurrentCallBodyPrefix

namespace DuplicatePrefix.CurrentCallResourceEntryFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver ReturnProtection
open CurrentCallResourceEntryBody
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

private theorem root_ext {first second : RootFrame} (same : first.frame = second.frame) : first = second := by
  cases first
  cases second
  cases same
  rfl

private theorem source_root (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (root : RootFrame) (borrowFrame : FrameState) (pointer : Pointer Provenance) (len : UInt64) (id : AllocId) (tag : BorTag) :
    CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len id tag =
      PositiveRootArguments.firstDone root
        (CurrentCallTypedSourceCopy.value options remaining span (CurrentCallTypedFnEntry.changedPointer pointer id tag) len).imm
        borrowFrame id tag := by
  apply root_ext
  simp only [CurrentCallSourceArguments.doneRoot,CurrentCallTypedSourceCopy.writtenFrame,CurrentCallTypedSourceCopy.copiedFrame,
    PositiveRootArguments.firstDone,PositiveRootArguments.protectedRoot,RootFrameData.write,
    TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,Array.set_set,Array.getElem_set_self,i1]

variable {options remaining span frames root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span frames root before tracker data owner id offset len W place}
    (out : Output limits C count)

/-- The actual generic resource entry ends at the existing installed-frame
representation, preserving the original return place and exact source value. -/
theorem installed_eq :
    CurrentCallResourceEntry.finishedFrame out = PositiveRootInstalledFrame.installed root
      (CurrentCallTypedSourceCopy.value options remaining span
        (CurrentCallTypedFnEntry.changedPointer W.pointer.value id tracker.global.nextPointerTag) len).imm
      count C.borrowFrame id tracker.global.nextPointerTag out.physical.id out.sourceOutput.global.nextPointerTag := by
  unfold CurrentCallResourceEntry.finishedFrame
  rw [out.argsRootEq,source_root,out.sourceFrame]
  rfl

/-- Exact pure fields of the actual post-entry machine. -/
theorem user_eq : out.finalMachine.user = before.user := by
  rw [out.finalMachineEq]
  change out.sourceMachine.user = before.user
  rw [out.sourceMachineEq]
  change {before.user with payload := {before.user.payload with ghost := false}} = before.user
  rw [←C.model.ghostOff]

theorem threads_eq : out.finalMachine.threads = before.threads := by
  rw [out.finalMachineEq]
  change out.sourceMachine.threads = before.threads
  rw [out.sourceMachineEq]
  rfl

theorem dataRace_eq : out.finalMachine.dataRace = before.dataRace := by
  rw [out.finalMachineEq]
  change out.sourceMachine.dataRace = before.dataRace
  rw [out.sourceMachineEq]
  rfl

/-- Actual entry restores the original Default mode with the UPDATED global;
all selected configuration and type-cache facts follow from exact user fields. -/
theorem model : DuplicatePrefixCallModel.Model options remaining span out.finalMachine := by
  have user := user_eq out
  have threads := threads_eq out
  have race := dataRace_eq out
  obtain ⟨old,enabled,mode⟩ := C.model.defaultTracker
  have equal : old = tracker := Option.some.inj (enabled.symm.trans C.state.enabled)
  subst old
  refine ⟨C.model.debugOff,C.model.preciseOff,C.model.implicitOff,?_,?_,?_,?_,?_,?_,?_,?_,?_,C.model.nullComparator,C.model.sourceMatches⟩
  · rw [user];exact C.model.ghostOff
  · rw [user];exact C.model.shallow
  · exact ⟨⟨out.boolOutput.global,tracker.retagMode⟩,out.finalTracked,mode⟩
  · rw [race];exact C.model.noDataRace
  · rw [user];exact C.model.noBackend
  · rw [user];exact C.model.metadata
  · rw [threads];exact C.model.fixedScheduler
  · rw [user];exact C.model.unchecked
  · rw [user];exact C.model.noGc

theorem origins : DuplicatePrefixTypeCacheOrigins.Origins out.finalMachine.user.payload.payload.user.types := by
  rw [user_eq out]
  exact C.origins

theorem size : (CurrentCallResourceEntry.finishedFrame out).locals.size = 25 := by
  rw [installed_eq out]
  exact PositiveRootInstalledFrame.size _ _ _ _ _ _ _ _

theorem slots (index : Fin 25) :
    (CurrentCallResourceEntry.finishedFrame out).locals[index.val]? = some (
      if 14 = index.val ∨ 13 = index.val ∨ 6 = index.val ∨ 0 = index.val then ⟨.live (.immediate .uninit),none⟩
      else if 2 = index.val then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
      else if 1 = index.val then ⟨.live (.immediate
        (CurrentCallTypedSourceCopy.value options remaining span
          (CurrentCallTypedFnEntry.changedPointer W.pointer.value id tracker.global.nextPointerTag) len).imm),some ActualReferenceMetadata.reference⟩
      else ⟨.dead,none⟩) := by
  rw [installed_eq out]
  exact PositiveRootInstalledFrame.slot_option _ C.rawLocals _ _ _ _ _ _ _ index

theorem immediate : CopyHelperCleanup.AllImmediate (CurrentCallResourceEntry.finishedFrame out) := by
  rw [installed_eq out]
  exact PositiveRootInstalledFrame.immediate _ C.rawLocals _ _ _ _ _ _ _

theorem source_local : (CurrentCallResourceEntry.finishedFrame out).locals[1]? = some ⟨.live (.immediate
    (CurrentCallTypedSourceCopy.value options remaining span
      (CurrentCallTypedFnEntry.changedPointer W.pointer.value id tracker.global.nextPointerTag) len).imm),some ActualReferenceMetadata.reference⟩ := by
  simpa using slots out ⟨1,by decide⟩

theorem count_local : (CurrentCallResourceEntry.finishedFrame out).locals[2]? =
    some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ := by
  simpa using slots out ⟨2,by decide⟩

theorem metadata :
    (CurrentCallResourceEntry.finishedFrame out).body = root.frame.body ∧
    (CurrentCallResourceEntry.finishedFrame out).bodyIdentity = root.frame.bodyIdentity ∧
    (CurrentCallResourceEntry.finishedFrame out).functionInstance = root.frame.functionInstance ∧
    (CurrentCallResourceEntry.finishedFrame out).returnContinuation = root.frame.returnContinuation ∧
    (CurrentCallResourceEntry.finishedFrame out).returnPlace = root.frame.returnPlace ∧
    (CurrentCallResourceEntry.finishedFrame out).vaList = root.frame.vaList ∧
    (CurrentCallResourceEntry.finishedFrame out).extra.dataRace = root.frame.extra.dataRace ∧
    (CurrentCallResourceEntry.finishedFrame out).extra.borrowTracker =
      some ((C.borrowFrame.addProtector id tracker.global.nextPointerTag).addProtector out.physical.id out.sourceOutput.global.nextPointerTag) ∧
    (CurrentCallResourceEntry.finishedFrame out).location = .mir ⟨0,0⟩ := by
  rw [installed_eq out]
  exact PositiveRootInstalledFrame.metadata _ _ _ _ _ _ _ _


theorem track : (CurrentCallResourceEntry.finishedFrame out).trackCallerArg = root.frame.trackCallerArg := by
  rw [installed_eq out]
  exact PositiveRootInstalledFrame.track _ _ _ _ _ _ _ _

theorem relevance : (CurrentCallResourceEntry.finishedFrame out).extra.userRelevance = root.frame.extra.userRelevance := by
  rw [installed_eq out]
  exact PositiveRootInstalledFrame.relevance _ _ _ _ _ _ _ _

end
end DuplicatePrefix.CurrentCallResourceEntryFacts
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallResourceEntryFacts.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved entry facts dependency {dependency}"
