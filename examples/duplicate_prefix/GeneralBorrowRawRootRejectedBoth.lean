import duplicate_prefix.GeneralBorrowRawRootToLenBoth
import duplicate_prefix.GeneralBorrowRawRootAcceptedBoth
import duplicate_prefix.GeneralBorrowRawRootTickRuntime
import duplicate_prefix.GeneralBorrowRawLenRejectedFrame
namespace DuplicatePrefix.GeneralBorrowRawRootRejectedBoth
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
abbrev Initial := GeneralBorrowRawRootZeroEntry.Initial

abbrev Heap := GeneralBorrowRawRootAcceptedBoth.Heap

structure Frame (entry result : CompilerFrameContext.ActualFrame) : Prop where
  body : result.body = RootBody.reflected.body.body
  identity : result.bodyIdentity = RootBody.reflected.body.identity
  callee : result.functionInstance = RootBody.reflected.functionInstance
  extra : result.extra = entry.extra
  returnPlace : result.returnPlace = entry.returnPlace
  continuation : result.returnContinuation = entry.returnContinuation
  varargs : result.vaList = entry.vaList
  localsIdentity : result.localsIdentity = entry.localsIdentity
  size : result.locals.size = 25
  location : result.location = .mir ⟨10,0⟩
  value : result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩
  immediate : CopyHelperCleanup.AllImmediate result

private theorem cell (frame : CompilerFrameContext.ActualFrame) (i : Nat) (valid : i < frame.locals.size)
    (row : LocalState Provenance LocalLayout) (present : frame.locals[i]? = some row) : frame.locals[i] = row :=
  Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans present)

/-- The rejected count branch from original call-time data. Initialization,
shared Ref, len, release/return and pure rejected guard are all actual traces. -/
theorem executes (s : Initial) (n : UInt64) (positiveCount : n ≠ 0) (rejected : n > s.len/2)
    (preciseOff : s.options.retag.preciseInteriorMut = false)
    (implicitOff : s.options.retag.implicitWrites = false)
    (budget : Nat) (dispatch : s.limits.callDispatch = budget+1)
    (nodeMargin : s.entry.allocation.extra.nodes.size+3 < 65536)
    (tagMargin : s.tracker.global.nextPointerTag.value.toNat+3 < 18446744073709551615) :
    ∃ (entryFrame result : CompilerFrameContext.ActualFrame)
      (initial post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      GeneralBorrowRawRootPositivePrefix.ActualCall s n entryFrame initial ∧
      entryFrame = GeneralBorrowRawRootInitialize.caller s n ∧
      SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits (Storage.withCurrent #[] entryFrame initial)
        (Storage.withCurrent #[] result post) ∧ Frame entryFrame result ∧ Nonempty (Heap s initial post) := by
  obtain ⟨entryFrame,callerFrame,returned,initial,machine,call,entryEq,trace,shape,⟨outcome⟩⟩ :=
    GeneralBorrowRawRootToLenBoth.executes s n positiveCount preciseOff implicitOff budget dispatch nodeMargin tagMargin
  let caller := GeneralBorrowRawRootLenCaller.caller s callerFrame shape.size
  have facts := GeneralBorrowRawRootLenCaller.of_shape s n entryFrame callerFrame entryEq shape
  have bounded (i : Fin 25) : i.val < caller.locals.size := by rw [facts.size];exact i.isLt
  have zero := cell caller 0 (bounded ⟨0,by decide⟩) _ facts.zero
  have seven := cell caller 7 (bounded ⟨7,by decide⟩) _ facts.seven
  have eight := cell caller 8 (bounded ⟨8,by decide⟩) _ facts.eight
  have nine := cell caller 9 (bounded ⟨9,by decide⟩) _ facts.nine
  have ten := cell caller 10 (bounded ⟨10,by decide⟩) _ facts.ten
  have twelve := cell caller 12 (bounded ⟨12,by decide⟩) _ facts.twelve
  have thirteen := cell caller 13 (bounded ⟨13,by decide⟩) _ facts.thirteen
  have fifteen := cell caller 15 (bounded ⟨15,by decide⟩) _ facts.fifteen
  have sixteen := cell caller 16 (bounded ⟨16,by decide⟩) _ facts.sixteen
  obtain ⟨result,guardTrace,bodyAfter,identityAfter,calleeAfter,extraAfter,placeAfter,continuationAfter,varargsAfter,
    localsIdentityAfter,sizeAfter,locationAfter,valueAfter,allAfter⟩ := GeneralBorrowRawLenRejectedFrame.executes
    s.options s.limits s.remaining s.span s.source s.debugOff s.validityFuel s.validationEq caller machine s.len n rejected facts.size
    (GeneralBorrowRawRootToLen.refValue s) (congrArg LocalState.value twelve)
    (congrArg LocalState.value thirteen) (congrArg LocalState.layout thirteen)
    (congrArg LocalState.value zero) (congrArg LocalState.layout zero)
    (congrArg LocalState.value seven)
    (congrArg LocalState.value eight) (congrArg LocalState.layout eight)
    (congrArg LocalState.value nine) (congrArg LocalState.layout nine)
    (congrArg LocalState.value ten) (congrArg LocalState.layout ten)
    facts.body facts.identity facts.callee facts.immediate facts.clocks outcome.tracker outcome.tracked outcome.mode
    outcome.runtime.ghost outcome.runtime.shallow outcome.runtime.unchecked outcome.runtime.noGc outcome.runtime.fixed
  have attributes := LenCallResultFrame.attributes caller (bounded ⟨11,by decide⟩) s.len
  let post := RootZeroCompleteState.tick s.options s.remaining s.span (RootZeroCompleteState.tick s.options s.remaining s.span (RootZeroCompleteState.tick s.options s.remaining s.span machine))
  have ledger := GeneralBorrowRawLenRejectedFrame.machine_ledger s.options s.remaining s.span machine
  have runtime := GeneralBorrowRawRootTickRuntime.preserves s _ (GeneralBorrowRawRootTickRuntime.preserves s _ (GeneralBorrowRawRootTickRuntime.preserves s machine outcome.runtime))
  have finalTrace : SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits
      (Storage.withCurrent #[] returned machine) (Storage.withCurrent #[] result post) := by
    simpa only [outcome.frameEq,GeneralBorrowRawRootToLenBoth.lenFrame,GeneralBorrowRawRootLenCaller.caller,caller,post,GeneralBorrowRawRootToLenBoth.refValue,GeneralBorrowRawRootToLen.refValue] using guardTrace
  refine ⟨entryFrame,result,initial,post,call,entryEq,SuccessfulTrace.append trace finalTrace,?_,?_⟩
  · refine ⟨bodyAfter.trans (attributes.1.trans facts.body),identityAfter.trans (attributes.2.1.trans facts.identity),
      calleeAfter.trans (attributes.2.2.1.trans facts.callee),extraAfter.trans (attributes.2.2.2.1.trans facts.extra),
      placeAfter.trans (attributes.2.2.2.2.2.1.trans facts.returnPlace),
      continuationAfter.trans (attributes.2.2.2.2.2.2.1.trans facts.continuation),
      varargsAfter.trans (attributes.2.2.2.2.2.2.2.2.1.trans facts.varargs),
      localsIdentityAfter.trans (attributes.2.2.2.2.1.trans facts.localsIdentity),
      sizeAfter,locationAfter,valueAfter,allAfter⟩
  · exact ⟨{
      tree:=outcome.tree,tracker:=outcome.tracker,child:=outcome.child,memory:=ledger.1.trans outcome.memory,
      tracked:=ledger.2.1.trans outcome.tracked,mode:=outcome.mode,formed:=outcome.formed,owner:=outcome.owner,observer:=outcome.observer,
      original:=outcome.original,originalActivity:=outcome.originalActivity,runtime:=runtime}⟩
end
end DuplicatePrefix.GeneralBorrowRawRootRejectedBoth
