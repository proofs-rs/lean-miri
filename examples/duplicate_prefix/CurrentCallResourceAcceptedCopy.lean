import duplicate_prefix.CurrentCallResourceCopyPrefix
import duplicate_prefix.CurrentCallResourceCopyInputs
namespace DuplicatePrefix.CurrentCallResourceAcceptedCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
open CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    {out : Output limits C count} {ready : CurrentCallResourceBodyReadiness.Ready C} {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
    {result : CurrentCallResourceLenReturn.Result out ready Q stage}
    (done : CurrentCallResourceAsMutInvoke.DefaultResult result)
    (fresh : done.nextTracker.global.nextPointerTag.value<18446744073709551615)
    (valid15 : (15 : MIR.LocalId)<done.frame.locals.size)
    (seed : CurrentCallResourceAsMutCall.Seed options limits remaining span done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15)
    (returned : CurrentCallResourceAsMutReturn.Returned done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed)

def sourceTree : BorrowTree:=CurrentCallResourceAsMutReturn.releasedTree done.current done.entry done.frame done.base
  (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed
def held : MachineHooks.BorrowState:=CurrentCallResourceAsMutReturn.postTracker done.current done.entry done.frame done.base
  (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed
def copiedTree : BorrowTree:=((sourceTree done fresh valid15 seed).performBorrowAccessRange
  (.concrete seed.output.tag) (Size.ofBytes (UInt64.ofNat offset)) (Size.ofBytes count) .Read
  (held done fresh valid15 seed).global.protectedTags .VisitChildrenOfAccessed).tree.performBorrowAccessRange
    (.concrete seed.output.tag) (Size.ofBytes (UInt64.ofNat offset+count)) (Size.ofBytes count) .Write
    (held done fresh valid15 seed).global.protectedTags .VisitChildrenOfAccessed |>.tree

/-- Evidence after the actual accepted copy. Physical storage and all caller
metadata refer to this one root-9 machine and this one copied allocation. -/
structure Result where
  frame : CompilerFrameContext.ActualFrame
  machine : Before
  allocation : Allocation Provenance BorrowTree
  trace : SuccessfulTrace.Trace (config options (remaining+1) span) limits
    (Storage.withCurrent #[] returned.root returned.machine) (Storage.withCurrent #[] frame machine)
  location : frame.location=.mir ⟨9,0⟩
  body : frame.body=returned.root.body
  identity : frame.bodyIdentity=returned.root.bodyIdentity
  callee : frame.functionInstance=returned.root.functionInstance
  destination : frame.returnPlace=returned.root.returnPlace
  continuation : frame.returnContinuation=returned.root.returnContinuation
  varargs : frame.vaList=returned.root.vaList
  extra : frame.extra=returned.root.extra
  immediate : CopyHelperCleanup.AllImmediate frame
  size : frame.locals.size=25
  slot17 : frame.locals[17]?=some ⟨.live (.immediate .uninit),none⟩
  slot18 : frame.locals[18]?=some ⟨.live (.immediate .uninit),some CopyHelperUnit.layout⟩
  slot19 : frame.locals[19]?=some ⟨.live (.immediate (.scalar (CurrentCallResourceAsMutReturn.value done.current done.entry done.frame done.base
    (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed))),some CopyCompilerFacts.sourcePointerLayout⟩
  slot21 : frame.locals[21]?=some ⟨.live (.immediate (.scalar (Scalar.fromPointer (config options (remaining+1) span).access.runtime.base
    (Pointer.new (Provenance.concrete id seed.output.tag) (Size.ofBytes (done.base+UInt64.ofNat offset+count)))))),some CopyCompilerFacts.destPointerLayout⟩
  slot24 : frame.locals[24]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  keep : ∀ index,index<16→frame.locals[index]?=returned.root.locals[index]?
  live : machine.memory.live.find? (fun row=>row.1==id)=some (id,⟨done.entry.kind,allocation⟩)
  byteSize : allocation.byteSize=done.current.allocation.byteSize
  length : allocation.len=done.current.allocation.len
  snapshot : AllocationCopy.snapshot allocation=(AllocationCopy.snapshot done.current.allocation).extract 0 (UInt64.ofNat offset+count).toNat ++
    (AllocationCopy.snapshot done.current.allocation).extract (UInt64.ofNat offset).toNat (UInt64.ofNat offset+count).toNat ++
    (AllocationCopy.snapshot done.current.allocation).extract (UInt64.ofNat offset+count+count).toNat done.current.allocation.len
  tree : allocation.extra=copiedTree done fresh valid15 seed
  physical : S02SameDestinationAcceptedCopyPhysical.Physical allocation
  tracked : machine.borrowTracker=some (held done fresh valid15 seed)
  model : DuplicatePrefixCallModel.Model options remaining span machine
  origins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types
  addresses : machine.user.addresses=returned.machine.user.addresses
  extras : machine.user.payload.payload.user.runtime.extras=returned.machine.user.payload.payload.user.runtime.extras
  active : ∃ thread,machine.threads.activeThread?=some thread
  memory : machine.memory=(CanonicalCopy.replaceAllocation (Storage.withCurrent #[] returned.root (AddOutput.machine options remaining span returned.machine)) id done.entry.kind allocation).machine.memory

/-- Original initialized source storage and selected profile metadata supply
all lower copy certificates; no access status is an input. -/
theorem finish (budget : Nat) (dispatch : limits.callDispatch=budget+1)
    (statementFuel : Nat) (statementEq : limits.validation=statementFuel+1)
    (nonzero : count≠0) (within : count≤len/2)
    (track : root.frame.trackCallerArg=none) (relevance : 0<root.frame.extra.userRelevance)
    (physical : OrdinaryPhysicalValidity.MutU8Slice W.allocation (UInt64.ofNat offset) len)
    (room : W.allocation.len+64<2^64)
    (profile : CurrentCallBoolProtection.WindowReady before id (UInt64.ofNat offset).toNat len.toNat) :
    Nonempty (Result done fresh valid15 seed returned):=by
  have trackNone : returned.root.trackCallerArg=none:=(CurrentCallResourceAsMutFacts.track done fresh valid15 seed returned).trans track
  have relevant : 0<returned.root.extra.userRelevance:=by rw [CurrentCallResourceAsMutFacts.relevance done fresh valid15 seed returned];exact relevance
  have storage:=CurrentCallResourceCopyInputs.storage done physical room
  have profileNow:=CurrentCallResourceCopyInputs.profile done fresh valid15 seed returned profile
  have bounded:=CurrentCallResourceCopyInputs.bounded (C:=C) within
  obtain ⟨frame,machine,allocation,trace,location,body,identity,callee,destination,continuation,varargs,extra,immediate,size,slot17,slot18,slot19,slot21,slot24,keep,live,bytes,length,snapshot,tree,valid,tracked,model,origins,addresses,extras,active,memory⟩:=
    CurrentCallResourceCopyPrefix.copied done fresh valid15 seed returned budget dispatch statementFuel statementEq nonzero within
      trackNone relevant storage profileNow bounded
  exact ⟨⟨frame,machine,allocation,trace,location,body,identity,callee,destination,continuation,varargs,extra,immediate,size,slot17,slot18,slot19,slot21,slot24,keep,live,bytes,length,snapshot,tree,valid,tracked,model,origins,addresses,extras,active,memory⟩⟩
/-- Starting at the actual Len-return root, derive Default reborrow, the
mutable helper call/release/pop, and the accepted copy through root block 9. -/
theorem invoke (budget : Nat) (dispatch : limits.callDispatch=budget+1)
    (statementFuel : Nat) (statementEq : limits.validation=statementFuel+1)
    (nonzero : count≠0) (within : count≤len/2)
    (track : root.frame.trackCallerArg=none) (relevance : 0<root.frame.extra.userRelevance)
    (physical : OrdinaryPhysicalValidity.MutU8Slice W.allocation (UInt64.ofNat offset) len)
    (room : W.allocation.len+64<2^64)
    (profile : CurrentCallBoolProtection.WindowReady before id (UInt64.ofNat offset).toNat len.toNat) :
    ∃ done : CurrentCallResourceAsMutInvoke.DefaultResult result,∃ fresh valid15,
      ∃ seed : CurrentCallResourceAsMutCall.Seed options limits remaining span done.current done.entry done.frame done.base
        (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15,
      ∃ returned : CurrentCallResourceAsMutReturn.Returned done.current done.entry done.frame done.base
        (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed,
      ∃ copied : Result done fresh valid15 seed returned,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] result.rootFrame result.machine) (Storage.withCurrent #[] copied.frame copied.machine):=by
  obtain ⟨done,fresh,valid15,seed,_⟩:=CurrentCallResourceAsMutInvoke.invoke result nonzero within budget dispatch
  obtain ⟨returned⟩:=CurrentCallResourceAsMutReturn.invoke done.current done.entry done.frame done.base
    (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed C.model.debugOff C.validationFuel C.validationEq
  obtain ⟨copied⟩:=finish done fresh valid15 seed returned budget dispatch statementFuel statementEq nonzero within track relevance physical room profile
  exact ⟨done,fresh,valid15,seed,returned,copied,SuccessfulTrace.append done.trace (SuccessfulTrace.append returned.trace copied.trace)⟩

end
end DuplicatePrefix.CurrentCallResourceAcceptedCopy
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceAcceptedCopy" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual accepted resource copy dependency {dependency}"
