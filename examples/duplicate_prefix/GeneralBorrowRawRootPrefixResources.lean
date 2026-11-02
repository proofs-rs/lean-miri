import duplicate_prefix.GeneralBorrowRawRootPositivePrefix
import duplicate_prefix.GeneralBorrowRawFnEntryOrder
namespace DuplicatePrefix.GeneralBorrowRawRootPrefixResources
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
abbrev Initial := GeneralBorrowRawRootZeroEntry.Initial

def bufferTree (s : Initial) : BorrowTree :=
  GeneralBorrowRawFnEntryArgument.finalTree s.entry.allocation.extra s.tracker s.parentTag s.offset s.len

def bufferGlobal (s : Initial) : Miri.TreeBorrows.GlobalState :=
  (held s.tracker s.fresh s.slotFresh).global

structure Resources (s : Initial) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) : Prop where
  memory : (RootZeroCompleteState.tick s.options s.remaining s.span machine).memory = machine.memory
  tracker : (RootZeroCompleteState.tick s.options s.remaining s.span machine).borrowTracker = some (held s.tracker s.fresh s.slotFresh)
  runtime : GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.before
    (RootZeroCompleteState.tick s.options s.remaining s.span machine)
  buffer : machine.memory.live.find? (fun row => row.1 == s.id) =
    some (s.id,{s.entry with allocation := s.entry.allocation.setExtra (bufferTree s)})
  formed : DuplicatePrefixBorrowContract.RuntimeFacts (bufferTree s) (bufferGlobal s)
  capacity : (bufferTree s).locations.size = s.entry.allocation.extra.locations.size
  roots : (bufferTree s).roots = s.entry.allocation.extra.roots
  growth : (bufferTree s).nodes.size ≤ s.entry.allocation.extra.nodes.size+1
  order : ∀ valid : 0 < (bufferTree s).roots.size, s.raw.selected ≠ (bufferTree s).roots[0]'valid →
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder (bufferTree s)
  short : (bufferTree s).nodes.size < 65536
  owner : ∃ child, (bufferTree s).indexOfTag s.tracker.global.nextPointerTag = some child ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive (bufferTree s) (bufferGlobal s).protectedTags
      (some child) (some s.raw.selected) s.raw.maximum s.offset s.len) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin (bufferTree s) child .Write s.offset (s.offset+s.len)

/-- Internal determinism adapter: callers of `executes` obtain this initialization
fact from the proved initializer, rather than supplying an operation-success
hypothesis to the function-safety theorem. -/
theorem of_call (s : Initial) (n : UInt64)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (call : GeneralBorrowRawRootPositivePrefix.ActualCall s n frame machine) : Resources s machine := by
  obtain ⟨initialized,post,release,actual,tracked,flags,location,size,body,countSlot,borrow,releaseId,releaseTag,releaseSlotId,
    releaseRoot,releaseChild,slotSize,slotLen,slotMask,slotProv,slotMut,frameEq,machineEq⟩ :=
    GeneralBorrowRawRootInitialize.initializes s n
  have same : machine = post := by
    have equality := congrArg (fun result : EStateM.Result StepError RootState Unit =>
      match result with | .ok _ state => some state.machine | _ => none) (call.symm.trans actual)
    exact Option.some.inj equality
  subst machine
  have tickFlags : GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.before
      (RootZeroCompleteState.tick s.options s.remaining s.span post) := by
    rw [machineEq]
    exact GenericFunctionEntryRuntime.facts s.options s.remaining s.span s.before s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len
      s.slotFresh s.slotId s.slotEntry s.slotRoot release.slot.allocation s.ghost s.shallow s.race s.noBackend s.thread s.active s.unchecked s.noGc s.fixed
  have tickTracked : (RootZeroCompleteState.tick s.options s.remaining s.span post).borrowTracker = some (held s.tracker s.fresh s.slotFresh) := by
    unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields s.options () (s.remaining+1) s.span).terminators]
    exact tracked
  have tickMemory : (RootZeroCompleteState.tick s.options s.remaining s.span post).memory = post.memory := by
    unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields s.options () (s.remaining+1) s.span).terminators]
  have buffer := GenericFunctionEntryState.buffer_lookup (RawRootInvocation.machine #[] s.before) s.tracker s.fresh s.id s.entry
    s.parentTag s.offset s.len s.slotFresh s.slotId s.slotEntry s.slotRoot release.slot.allocation s.separate.symm
  rw [←machineEq] at buffer
  let fixedRaw : GeneralBorrowRawFnEntry.Input s.entry.allocation.extra s.tracker.global :=
    {s.raw with
      parentTag:=s.parentTag,offset:=s.offset,len:=s.len,
      tagged:=by rw [←s.rawTag];exact s.raw.tagged,
      positive:=by simpa only [s.rawOffset,s.rawLen] using s.raw.positive}
  obtain ⟨afterRuntime,capacity,growth,roots,heldTag,fresh,child,lookup,owner,activity⟩ :=
    GeneralBorrowRawRootEntryResources.resources s.entry.allocation.extra s.tracker {} s.id s.slotId s.runtime fixedRaw s.slotFresh
  obtain ⟨order,short⟩ := GeneralBorrowRawFnEntryOrder.conditional s.entry.allocation.extra s.tracker {} s.id s.runtime fixedRaw s.nodeHeadroom
  exact ⟨tickMemory,tickTracked,tickFlags,buffer,afterRuntime,capacity,roots,growth,order,short,child,lookup,owner,activity⟩

/-- Original call-time conditions derive both the actual positive-count trace
and every current buffer/runtime condition; no successful step is an input. -/
theorem executes (s : Initial) (n : UInt64) (positiveCount : n ≠ 0) :
    ∃ (entryFrame result : CompilerFrameContext.ActualFrame)
      (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      GeneralBorrowRawRootPositivePrefix.ActualCall s n entryFrame machine ∧
      entryFrame = GeneralBorrowRawRootInitialize.caller s n ∧
      SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits (Storage.withCurrent #[] entryFrame machine)
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick s.options s.remaining s.span machine)) ∧
      GenericFunctionEntryPrefix.Shape entryFrame result n ∧ Resources s machine := by
  obtain ⟨frame,result,machine,call,same,trace,shape⟩ := GeneralBorrowRawRootPositivePrefix.executes s n positiveCount
  exact ⟨frame,result,machine,call,same,trace,shape,of_call s n frame machine call⟩
end
end DuplicatePrefix.GeneralBorrowRawRootPrefixResources
