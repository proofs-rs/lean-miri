import duplicate_prefix.S02SeparateDestinationInstalledLocals

namespace DuplicatePrefix.S02SeparateDestinationRejectedPurePrefix
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- From the installed frame's exact local packet, the real nonzero-count MIR
prefix reaches block 2, statement 11. The machine settings are current-state
facts to be transported from the initial contract, not future success facts. -/
theorem executes_from_installed_locals
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (validation : options.limits.validation = fuel+1)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (count : UInt64) (nonzero : count ≠ 0)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨0,0⟩)
    (size : frame.locals.size = 25)
    (sourceValue : Immediate Provenance)
    (slots : ∀ i : Fin 25, frame.locals[i.val]? = some (
      if 14 = i.val ∨ 13 = i.val ∨ 6 = i.val ∨ 0 = i.val then ⟨.live (.immediate .uninit),none⟩
      else if 2 = i.val then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
      else if 1 = i.val then ⟨.live (.immediate sourceValue),some ActualReferenceMetadata.reference⟩
      else ⟨.dead,none⟩))
    (noClocks : frame.extra.dataRace = none)
    (immediate : CopyHelperCleanup.AllImmediate frame)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    ∃ result,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine)
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span machine)) ∧
      GenericFunctionEntryPrefix.Shape frame result count := by
  have cell (i : Fin 25) : frame.locals[i.val]'(by rw [size]; exact i.isLt) =
      if 14 = i.val ∨ 13 = i.val ∨ 6 = i.val ∨ 0 = i.val then ⟨.live (.immediate .uninit),none⟩
      else if 2 = i.val then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
      else if 1 = i.val then ⟨.live (.immediate sourceValue),some ActualReferenceMetadata.reference⟩
      else ⟨.dead,none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (by rw [size]; exact i.isLt)).symm.trans (slots i))
  have slot2 : frame.locals[2]'(by omega) =
      (⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ : LocalState Provenance LocalLayout) := by
    simpa using cell ⟨2,by decide⟩
  have dead (i : Fin 25) (different : i.val ≠ 0 ∧ i.val ≠ 1 ∧ i.val ≠ 2 ∧ i.val ≠ 6 ∧ i.val ≠ 13 ∧ i.val ≠ 14) :
      frame.locals[i.val]'(by rw [size]; exact i.isLt) = (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
    simpa [Ne.symm different.1,Ne.symm different.2.1,Ne.symm different.2.2.1,
      Ne.symm different.2.2.2.1,Ne.symm different.2.2.2.2.1,
      Ne.symm different.2.2.2.2.2] using cell i
  have d3 := dead ⟨3,by decide⟩ (by decide)
  have d4 := dead ⟨4,by decide⟩ (by decide)
  have d5 := dead ⟨5,by decide⟩ (by decide)
  have unused : ∀ id (valid : id < frame.locals.size), 7 ≤ id → id ≤ 12 →
      frame.locals[id]'valid = (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
    intro id valid lower upper
    have bounded : id < 25 := by rw [←size]; exact valid
    have different : id ≠ 0 ∧ id ≠ 1 ∧ id ≠ 2 ∧ id ≠ 6 ∧ id ≠ 13 ∧ id ≠ 14 := by
      repeat' constructor <;> omega
    have h := dead ⟨id,bounded⟩ different
    simpa only [Fin.val_mk] using h
  exact GenericFunctionEntryPrefix.executes_preserving options limits remaining span source debug fuel validation
    frame machine count nonzero size (congrArg LocalState.value slot2) (congrArg LocalState.layout slot2)
    (congrArg LocalState.value d3) (congrArg LocalState.layout d3)
    (congrArg LocalState.value d4) (congrArg LocalState.value d5)
    (congrArg LocalState.layout d4) (congrArg LocalState.layout d5)
    unused body identity callee location noClocks immediate tracker tracked defaultMode ghost shallow unchecked noGc fixed

end
end DuplicatePrefix.S02SeparateDestinationRejectedPurePrefix

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationRejectedPurePrefix.executes_from_installed_locals) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved rejected pure-prefix dependency {dependency}"
