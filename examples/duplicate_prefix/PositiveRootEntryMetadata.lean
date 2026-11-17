import duplicate_prefix.PositiveRootInstalledFrame

namespace DuplicatePrefix.PositiveRootEntryMetadata
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

set_option autoImplicit false in
/-- Data facts about the frame installed by the genuine root invocation. -/
structure Shape (frame : CompilerFrameContext.ActualFrame) (place : MPlaceTy Provenance) : Prop where
  body : frame.body = RootBody.reflected.body.body
  identity : frame.bodyIdentity = RootBody.reflected.body.identity
  callee : frame.functionInstance = RootBody.reflected.functionInstance
  noClocks : frame.extra.dataRace = none
  continuation : frame.returnContinuation = .stop true
  varargs : frame.vaList = #[]
  zero : frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩
  returnPlace : frame.returnPlace = .memory place
  trackNone : frame.trackCallerArg = none
  relevant : 0 < frame.extra.userRelevance

set_option autoImplicit false in
/-- Transport the original caller's address and allocation-extra contracts
through frame installation, whose fresh identity is otherwise irrelevant here. -/
structure MachineShape
    (before installed : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) : Prop where
  addresses : installed.user.addresses = before.user.addresses
  backend : installed.user.payload.payload.user.backend = before.user.payload.payload.user.backend
  extras : installed.user.payload.payload.user.runtime.extras = before.user.payload.payload.user.runtime.extras

set_option autoImplicit false in
theorem installed (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) (noRace : before.dataRace = none)
    (adjusted : Immediate Provenance) (count : UInt64)
    (id : AllocId) (bufferChild : BorTag) (slotId : AllocId) (slotChild : BorTag) :
    Shape (PositiveRootInstalledFrame.installed (RawRootInvocation.root before place noRace)
      adjusted count {} id bufferChild slotId slotChild) place := by
  let raw := RawRootInvocation.root before place noRace
  obtain ⟨body,identity,callee,continuation,destination,varargs,race,_,_⟩ :=
    PositiveRootInstalledFrame.metadata raw adjusted count {} id bufferChild slotId slotChild
  have control := RawRootInvocation.control before place noRace
  have zero := PositiveRootInstalledFrame.slot_option raw (RawRootInvocation.locals before place noRace)
    adjusted count {} id bufferChild slotId slotChild ⟨0,by decide⟩
  simp only [Fin.val_mk,eq_self_iff_true,Nat.reduceEqDiff,or_true,or_false,true_or,false_or,ite_true,ite_false] at zero
  refine ⟨body.trans raw.body,identity.trans raw.identity,callee.trans raw.callee,race.trans raw.noClocks,
    continuation.trans control.2.2.1,varargs.trans (by rfl),zero,destination.trans control.2.2.2,
    (PositiveRootInstalledFrame.track raw adjusted count {} id bufferChild slotId slotChild).trans control.2.1,?_⟩
  have same := (PositiveRootInstalledFrame.relevance raw adjusted count {} id bufferChild slotId slotChild).trans
    (PositiveRootInstalledFrame.raw_relevance before place noRace)
  rw [same]
  decide

set_option autoImplicit false in
theorem of_same_user (before installed : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (same : installed.user = (RawRootInvocation.machine #[] before).user) : MachineShape before installed := by
  have fields := RawRootInvocation.preservation #[] before
  exact ⟨(congrArg (fun user : Machine.RootUser => user.addresses) same).trans fields.2.2.2.1,
    (congrArg (fun user : Machine.RootUser => user.payload.payload.user.backend) same).trans fields.2.2.2.2.2.2.2.1,
    (congrArg (fun user : Machine.RootUser => user.payload.payload.user.runtime.extras) same).trans fields.2.2.2.2.2.2.2.2⟩

end DuplicatePrefix.PositiveRootEntryMetadata
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.PositiveRootEntryMetadata.installed,
      ``DuplicatePrefix.PositiveRootEntryMetadata.of_same_user] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved positive root installation metadata dependency {dependency}"
