import duplicate_prefix.GeneralBorrowRawRootInitialize
import duplicate_prefix.GenericFunctionEntryPrefix
import duplicate_prefix.GeneralBorrowRawRootEntryResources
namespace DuplicatePrefix.GeneralBorrowRawRootPositivePrefix
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def ActualCall (s : GeneralBorrowRawRootZeroEntry.Initial) (n : UInt64)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) : Prop :=
  Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
    RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
    #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
      (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
      ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second n)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ =
    .ok () (Storage.withCurrent #[] frame machine)

/-- Actual initialization and all pure statements up to the shared Ref site.
The memory and tracker stay in the exact ticked initializer machine. -/
theorem executes (s : GeneralBorrowRawRootZeroEntry.Initial) (n : UInt64) (positiveCount : n ≠ 0) :
    ∃ (entryFrame result : CompilerFrameContext.ActualFrame)
      (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      ActualCall s n entryFrame machine ∧
      entryFrame = GeneralBorrowRawRootInitialize.caller s n ∧
      SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits (Storage.withCurrent #[] entryFrame machine)
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick s.options s.remaining s.span machine)) ∧
      GenericFunctionEntryPrefix.Shape entryFrame result n := by
  obtain ⟨frame,machine,release,call,tracked,flags,location,size,body,countSlot,borrow,releaseId,releaseTag,releaseSlotId,
    releaseRoot,releaseChild,slotSize,slotLen,slotMask,slotProv,slotMut,frameEq,machineEq⟩ :=
    GeneralBorrowRawRootInitialize.initializes s n
  let raw := RawRootInvocation.root s.before s.place s.race
  let adjusted := (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
    (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm
  have exactFrame : frame = PositiveRootInstalledFrame.installed raw adjusted n {} s.id s.tracker.global.nextPointerTag
      s.slotId (next s.tracker s.fresh).global.nextPointerTag := frameEq
  have slots (i : Fin 25) := PositiveRootInstalledFrame.slot_option raw (RawRootInvocation.locals s.before s.place s.race)
    adjusted n {} s.id s.tracker.global.nextPointerTag s.slotId (next s.tracker s.fresh).global.nextPointerTag i
  let row (i : Fin 25) : LocalState Provenance LocalLayout :=
    if 14 = i.val ∨ 13 = i.val ∨ 6 = i.val ∨ 0 = i.val then ⟨.live (.immediate .uninit),none⟩
    else if 2 = i.val then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩
    else if 1 = i.val then ⟨.live (.immediate adjusted),some ActualReferenceMetadata.reference⟩
    else ⟨.dead,none⟩
  have cell (i : Fin 25) : frame.locals[i.val]? = some (row i) := by rw [exactFrame];exact slots i
  have atCell (i : Fin 25) : frame.locals[i.val] = row i :=
    Option.some.inj ((Array.getElem?_eq_getElem (by rw [size];exact i.isLt)).symm.trans (cell i))
  obtain ⟨fb,fi,fc,frc,frp,fva,frace,fborrow,floc⟩ :=
    PositiveRootInstalledFrame.metadata raw adjusted n {} s.id s.tracker.global.nextPointerTag s.slotId (next s.tracker s.fresh).global.nextPointerTag
  have identity : frame.bodyIdentity = RootBody.reflected.body.identity := by rw [exactFrame,fi];exact raw.identity
  have callee : frame.functionInstance = RootBody.reflected.functionInstance := by rw [exactFrame,fc];exact raw.callee
  have clocks : frame.extra.dataRace = none := by rw [exactFrame,frace];exact raw.noClocks
  have immediate : CopyHelperCleanup.AllImmediate frame := by
    rw [exactFrame]
    exact PositiveRootInstalledFrame.immediate raw (RawRootInvocation.locals s.before s.place s.race)
      adjusted n {} s.id s.tracker.global.nextPointerTag s.slotId (next s.tracker s.fresh).global.nextPointerTag
  have unused : ∀ id (valid : id < frame.locals.size), 7 ≤ id → id ≤ 12 → frame.locals[id] = ⟨.dead,none⟩ := by
    intro id valid low high
    have bound : id < 25 := by omega
    have value := atCell ⟨id,bound⟩
    change frame.locals[id] = (if 14 = id ∨ 13 = id ∨ 6 = id ∨ 0 = id then _ else if 2 = id then _ else if 1 = id then _ else _) at value
    have no0 : 0 ≠ id := by omega
    have no1 : 1 ≠ id := by omega
    have no2 : 2 ≠ id := by omega
    have no6 : 6 ≠ id := by omega
    have no13 : 13 ≠ id := by omega
    have no14 : 14 ≠ id := by omega
    simpa only [no0,no1,no2,no6,no13,no14,or_self,ite_false] using value
  obtain ⟨result,trace,shape⟩ := GenericFunctionEntryPrefix.executes_preserving s.options s.limits s.remaining s.span s.source
    s.debugOff s.validityFuel s.validationEq frame machine n positiveCount size
    (by simpa only [row,Nat.reduceEqDiff,or_self,ite_false,ite_true] using congrArg LocalState.value (atCell ⟨2,by decide⟩))
    (by simpa only [row,Nat.reduceEqDiff,or_self,ite_false,ite_true] using congrArg LocalState.layout (atCell ⟨2,by decide⟩))
    (by simpa only [row,Nat.reduceEqDiff,or_self,ite_false,ite_true] using congrArg LocalState.value (atCell ⟨3,by decide⟩))
    (by simpa only [row,Nat.reduceEqDiff,or_self,ite_false,ite_true] using congrArg LocalState.layout (atCell ⟨3,by decide⟩))
    (by simpa only [row,Nat.reduceEqDiff,or_self,ite_false,ite_true] using congrArg LocalState.value (atCell ⟨4,by decide⟩))
    (by simpa only [row,Nat.reduceEqDiff,or_self,ite_false,ite_true] using congrArg LocalState.value (atCell ⟨5,by decide⟩))
    (by simpa only [row,Nat.reduceEqDiff,or_self,ite_false,ite_true] using congrArg LocalState.layout (atCell ⟨4,by decide⟩))
    (by simpa only [row,Nat.reduceEqDiff,or_self,ite_false,ite_true] using congrArg LocalState.layout (atCell ⟨5,by decide⟩)) unused body identity callee location clocks immediate
    (held s.tracker s.fresh s.slotFresh) tracked s.mode flags.ghost flags.shallow flags.unchecked flags.noGc flags.fixed
  exact ⟨frame,result,machine,call,frameEq,trace,shape⟩
end
end DuplicatePrefix.GeneralBorrowRawRootPositivePrefix
