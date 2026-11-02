import duplicate_prefix.CurrentCallSpatialEntry
import duplicate_prefix.CurrentCallBodyPrefix

namespace DuplicatePrefix.CurrentCallSpatialEntryFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver ReturnProtection
open CurrentCallSpatialEntry
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

variable {options remaining span frames root before tracker ctx offset len source returnOffset ret place limits count}
    {C : Conditions options remaining span frames root before tracker ctx offset len source returnOffset ret place}
    (out : Output C limits count)

def machine : Before := CurrentCallSpatialEntry.finalMachine place _ out.physical
  (protectedState C count out.entry out.physical out.fresh out.boolOutput) out.updated

def finishedFrame : CompilerFrameContext.ActualFrame := CallEntryFacts.doneRootFrame
  {registeredFrame (atSpan (argsRoot C count) ⟨601⟩).frame (sourceOutput C).frame
    out.physical.id (sourceOutput C).global.nextPointerTag with location:=.unwinding ⟨559⟩}

/-- The actual generic resource entry ends at the existing installed-frame
representation, preserving the original return place and exact source value. -/
theorem installed_eq :
    finishedFrame out = PositiveRootInstalledFrame.installed root
      (CurrentCallTypedSourceCopy.value options remaining span
        (CurrentCallTypedFnEntry.changedPointer source.family.value source.backing.id tracker.global.nextPointerTag) len).imm
      count C.borrowFrame source.backing.id tracker.global.nextPointerTag out.physical.id (sourceOutput C).global.nextPointerTag := by
  unfold finishedFrame CurrentCallSpatialEntry.argsRoot
  rw [source_root]
  rfl

/-- Pure actual post-entry fields, independent of every ownership map. -/
theorem user_eq : (machine out).user=before.user := by
  change {before.user with payload:={before.user.payload with ghost:=false}}=before.user
  rw [←C.model.ghostOff]

theorem threads_eq : (machine out).threads=before.threads := rfl

theorem dataRace_eq : (machine out).dataRace=before.dataRace := rfl

theorem finalTracked : (machine out).borrowTracker=some ⟨out.boolOutput.global,tracker.retagMode⟩ := by
  rw [out.boolGlobal]
  rfl

/-- Actual entry restores the original Default mode with the UPDATED global;
all selected configuration and type-cache facts follow from exact user fields. -/
theorem model : DuplicatePrefixCallModel.Model options remaining span (machine out) := by
  have user := user_eq out
  have threads := threads_eq out
  have race := dataRace_eq out
  obtain ⟨old,enabled,mode⟩ := C.model.defaultTracker
  have equal : old = tracker := Option.some.inj (enabled.symm.trans C.state.enabled)
  subst old
  refine ⟨C.model.debugOff,C.model.preciseOff,C.model.implicitOff,?_,?_,?_,?_,?_,?_,?_,?_,?_,C.model.nullComparator,C.model.sourceMatches⟩
  · rw [user];exact C.model.ghostOff
  · rw [user];exact C.model.shallow
  · exact ⟨⟨out.boolOutput.global,tracker.retagMode⟩,finalTracked out,mode⟩
  · rw [race];exact C.model.noDataRace
  · rw [user];exact C.model.noBackend
  · rw [user];exact C.model.metadata
  · rw [threads];exact C.model.fixedScheduler
  · rw [user];exact C.model.unchecked
  · rw [user];exact C.model.noGc

theorem origins : DuplicatePrefixTypeCacheOrigins.Origins (machine out).user.payload.payload.user.types := by
  rw [user_eq out]
  exact C.origins

theorem size : (finishedFrame out).locals.size = 25 := by
  rw [installed_eq out]
  exact PositiveRootInstalledFrame.size _ _ _ _ _ _ _ _

theorem slots (index : Fin 25) :
    (finishedFrame out).locals[index.val]? = some (
      if 14 = index.val ∨ 13 = index.val ∨ 6 = index.val ∨ 0 = index.val then ⟨.live (.immediate .uninit),none⟩
      else if 2 = index.val then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
      else if 1 = index.val then ⟨.live (.immediate
        (CurrentCallTypedSourceCopy.value options remaining span
          (CurrentCallTypedFnEntry.changedPointer source.family.value source.backing.id tracker.global.nextPointerTag) len).imm),some ActualReferenceMetadata.reference⟩
      else ⟨.dead,none⟩) := by
  rw [installed_eq out]
  exact PositiveRootInstalledFrame.slot_option _ C.rawLocals _ _ _ _ _ _ _ index

theorem immediate : CopyHelperCleanup.AllImmediate (finishedFrame out) := by
  rw [installed_eq out]
  exact PositiveRootInstalledFrame.immediate _ C.rawLocals _ _ _ _ _ _ _

theorem source_local : (finishedFrame out).locals[1]? = some ⟨.live (.immediate
    (CurrentCallTypedSourceCopy.value options remaining span
      (CurrentCallTypedFnEntry.changedPointer source.family.value source.backing.id tracker.global.nextPointerTag) len).imm),some ActualReferenceMetadata.reference⟩ := by
  simpa using slots out ⟨1,by decide⟩

theorem count_local : (finishedFrame out).locals[2]? =
    some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ := by
  simpa using slots out ⟨2,by decide⟩

theorem metadata :
    (finishedFrame out).body = root.frame.body ∧
    (finishedFrame out).bodyIdentity = root.frame.bodyIdentity ∧
    (finishedFrame out).functionInstance = root.frame.functionInstance ∧
    (finishedFrame out).returnContinuation = root.frame.returnContinuation ∧
    (finishedFrame out).returnPlace = root.frame.returnPlace ∧
    (finishedFrame out).vaList = root.frame.vaList ∧
    (finishedFrame out).extra.dataRace = root.frame.extra.dataRace ∧
    (finishedFrame out).extra.borrowTracker =
      some ((C.borrowFrame.addProtector source.backing.id tracker.global.nextPointerTag).addProtector out.physical.id (sourceOutput C).global.nextPointerTag) ∧
    (finishedFrame out).location = .mir ⟨0,0⟩ := by
  rw [installed_eq out]
  exact PositiveRootInstalledFrame.metadata _ _ _ _ _ _ _ _


theorem track : (finishedFrame out).trackCallerArg = root.frame.trackCallerArg := by
  rw [installed_eq out]
  exact PositiveRootInstalledFrame.track _ _ _ _ _ _ _ _

theorem relevance : (finishedFrame out).extra.userRelevance = root.frame.extra.userRelevance := by
  rw [installed_eq out]
  exact PositiveRootInstalledFrame.relevance _ _ _ _ _ _ _ _

theorem before_zero_return (zero : count=0) :
    ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] (finishedFrame out) (machine out))
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span
          (RootZeroCompleteState.tick options remaining span (machine out)))) ∧
      result.body=RootBody.reflected.body.body ∧ result.bodyIdentity=RootBody.reflected.body.identity ∧
      result.functionInstance=RootBody.reflected.functionInstance ∧ result.locals.size=25 ∧ result.location=.mir ⟨10,0⟩ ∧
      result.locals[0]?=some ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ ∧
      result.returnPlace=(finishedFrame out).returnPlace ∧
      result.extra=(finishedFrame out).extra ∧
      result.returnContinuation=(finishedFrame out).returnContinuation ∧
      result.vaList=(finishedFrame out).vaList ∧ CopyHelperCleanup.AllImmediate result :=
  (CurrentCallBodyPrefix.body_prefix_of_installed options limits remaining span root C.rawLocals
  (CurrentCallTypedSourceCopy.value options remaining span
    (CurrentCallTypedFnEntry.changedPointer source.family.value source.backing.id tracker.global.nextPointerTag) len).imm
  count C.borrowFrame source.backing.id tracker.global.nextPointerTag out.physical.id (sourceOutput C).global.nextPointerTag
  (finishedFrame out) (machine out) (installed_eq out)
  (model out) C.validationFuel C.validationEq).1 zero

end
end DuplicatePrefix.CurrentCallSpatialEntryFacts
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallSpatialEntryFacts.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved entry facts dependency {dependency}"
