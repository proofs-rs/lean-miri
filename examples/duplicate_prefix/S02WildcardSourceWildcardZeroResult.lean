import duplicate_prefix.S02WildcardSourceWildcardInstalledBoth
import duplicate_prefix.S02WildcardSourceWildcardZeroControl
import duplicate_prefix.S04ZeroCountBodyActiveWildcardBounds
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.SuccessfulTraceTerminal
import duplicate_prefix.DuplicatePrefixArgumentCallResult

namespace DuplicatePrefix.S02WildcardSourceWildcardZeroResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Original full call Result for count zero, positive wildcard source and a
distinct wildcard return allocation. The body and Return are actual steps. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len),
      reference.id ≠ input.contract.destination.id →
      DuplicatePrefixArgumentCallResult.Result options limits remaining span before
        (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len 0 place := by
  obtain ⟨reference,output,firstFresh,ready⟩ :=
    S02WildcardSourceWildcardInstalledBoth.enters_identity
      address len 0 input nonempty returnWildcard
  refine ⟨reference,?_⟩
  intro different
  obtain ⟨destination,secondFresh,tree,updated,actual,destId,
    ⟨returnPacket,packetId,⟨sourcePacket⟩⟩⟩ := ready different
  let rawMachine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine rawMachine reference.tracker firstFresh
    reference.id reference.entry output.child.tree
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) 0).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let borrowFrame := owned.addProtector destination.id destination.tracker.global.nextPointerTag
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
    destination.tracker.global.nextPointerTag
  let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  obtain ⟨settings⟩ := S02WildcardSourceWildcardZeroControl.at_protection address len
    input reference output firstFresh destination destId secondFresh tree updated
  have trackerEq : sourcePacket.tracker = settings.tracker :=
    Option.some.inj (sourcePacket.enabled.symm.trans settings.enabled)
  have returnTrackerEq : returnPacket.tracker = settings.tracker :=
    Option.some.inj (returnPacket.enabled.symm.trans settings.enabled)
  have separate : returnPacket.destination.id ≠ reference.id := by
    rw [packetId,destId]
    exact Ne.symm different
  have extras : after.machine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == returnPacket.destination.id) =
        some (returnPacket.destination.id,⟨none,#[]⟩) := by
    rw [packetId]
    exact settings.extras
  have outside : ∀ row ∈ (#[] : Array (Size × MemoryExtras.Entry Unit)),
      row.1.bytes.toNat < returnPacket.destination.offset.toNat ∨
        returnPacket.destination.offset.toNat + 1 ≤ row.1.bytes.toNat := by simp
  have frameEq : installed = PositiveRootInstalledFrame.installed root adjusted 0 {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag := rfl
  have metadata := PositiveRootInstalledFrame.metadata root adjusted 0 {}
    reference.id reference.tracker.global.nextPointerTag destination.id
    destination.tracker.global.nextPointerTag
  have size := PositiveRootInstalledFrame.size root adjusted 0 {}
    reference.id reference.tracker.global.nextPointerTag destination.id
    destination.tracker.global.nextPointerTag
  have slots := PositiveRootInstalledFrame.slot_option root
    (RawRootInvocation.locals before place input.contract.model.noDataRace) adjusted 0 {}
    reference.id reference.tracker.global.nextPointerTag destination.id
    destination.tracker.global.nextPointerTag
  have immediate := PositiveRootInstalledFrame.immediate root
    (RawRootInvocation.locals before place input.contract.model.noDataRace) adjusted 0 {}
    reference.id reference.tracker.global.nextPointerTag destination.id
    destination.tracker.global.nextPointerTag
  have frameSize : installed.locals.size = 25 := by rw [frameEq]; exact size
  have slot0 : installed.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ := by
    rw [frameEq]; simpa using slots ⟨0,by decide⟩
  have slot2 : installed.locals[2]? = some
      ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))),some RootCompilerFacts.usizeLayout⟩ := by
    rw [frameEq]; simpa using slots ⟨2,by decide⟩
  have slot3 : installed.locals[3]? = some ⟨.dead,none⟩ := by
    rw [frameEq]; simpa using slots ⟨3,by decide⟩
  have slot4 : installed.locals[4]? = some ⟨.dead,none⟩ := by
    rw [frameEq]; simpa using slots ⟨4,by decide⟩
  have slot5 : installed.locals[5]? = some ⟨.dead,none⟩ := by
    rw [frameEq]; simpa using slots ⟨5,by decide⟩
  have body : installed.body = RootBody.reflected.body.body := by
    rw [frameEq]; exact metadata.1.trans root.body
  have identity : installed.bodyIdentity = RootBody.reflected.body.identity := by
    rw [frameEq]; exact metadata.2.1.trans root.identity
  have callee : installed.functionInstance = RootBody.reflected.functionInstance := by
    rw [frameEq]; exact metadata.2.2.1.trans root.callee
  have location : installed.location = .mir ⟨0,0⟩ := by
    rw [frameEq]; exact metadata.2.2.2.2.2.2.2.2
  have noClocks : installed.extra.dataRace = none := by
    rw [frameEq]; exact metadata.2.2.2.2.2.2.1.trans root.noClocks
  have returnPlace : installed.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ := by
    rw [frameEq,metadata.2.2.2.2.1,
      (RawRootInvocation.control before place input.contract.model.noDataRace).2.2.2]
    rfl
  have continuation : installed.returnContinuation = .stop true := by
    rw [frameEq,metadata.2.2.2.1]
    exact (RawRootInvocation.control before place input.contract.model.noDataRace).2.2.1
  have immediateLocals : CopyHelperCleanup.AllImmediate installed := by
    rw [frameEq]; exact immediate
  have varargs : installed.vaList = #[] := by
    rw [frameEq,metadata.2.2.2.2.2.1]
    rfl
  have frameTracked : installed.extra.borrowTracker = some borrowFrame := by
    rw [frameEq]
    exact metadata.2.2.2.2.2.2.2.1
  have localValue (i : Fin 25) := slots i
  have localSlot (i : Fin 25) : installed.locals[i.val]'(by rw [frameSize]; exact i.isLt) =
      if 14 = i.val ∨ 13 = i.val ∨ 6 = i.val ∨ 0 = i.val then ⟨.live (.immediate .uninit),none⟩
      else if 2 = i.val then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))),some RootCompilerFacts.usizeLayout⟩
      else if 1 = i.val then ⟨.live (.immediate adjusted),some ActualReferenceMetadata.reference⟩
      else ⟨.dead,none⟩ := by
    exact Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize]; exact i.isLt)).symm.trans
      (by rw [frameEq]; exact localValue i))
  have slot0Row : installed.locals[0]'(by rw [frameSize];decide) =
      ⟨.live (.immediate .uninit),none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).symm.trans slot0)
  have slot2Row : installed.locals[2]'(by rw [frameSize];decide) =
      ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))),some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).symm.trans slot2)
  have slot3Row : installed.locals[3]'(by rw [frameSize];decide) = (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
    Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).symm.trans slot3)
  have slot4Row : installed.locals[4]'(by rw [frameSize];decide) = (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
    Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).symm.trans slot4)
  have slot5Row : installed.locals[5]'(by rw [frameSize];decide) = (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
    Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).symm.trans slot5)
  have source := DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model
  let sourceEntry := sourcePacket.entry
  obtain ⟨done,trace,terminal,empty,noErrors,noUB⟩ :=
    S04ZeroCountBodyActiveWildcardBounds.complete_active_wildcard options limits remaining span
      installed after.machine settings.tracker borrowFrame settings.mode settings.enabled frameTracked
      place returnPacket.destination returnPacket.returnTag returnPacket.child returnPacket.node
      reference.id sourceEntry separate sourcePacket.live
      reference.tracker.global.nextPointerTag sourcePacket.child sourcePacket.child
      (some reference.tracker.global.nextPointerTag)
      reference.offset len sourcePacket.node sourcePacket.tagged sourcePacket.present sourcePacket.hidden
      (by rw [←trackerEq]; exact sourcePacket.runtime)
      (by rw [←trackerEq]; exact sourcePacket.positive)
      sourcePacket.distinct (by intro _ _; exact sourcePacket.order) sourcePacket.short sourcePacket.activity
      returnPacket.owned returnPacket.tagged returnPacket.present returnPacket.same
      returnPacket.parentless returnPacket.leaf returnPacket.hidden returnPacket.hiddenFrame
      (by rw [←returnTrackerEq]; exact returnPacket.runtime)
      (by rw [←returnTrackerEq]; exact returnPacket.positive)
      returnPacket.distinct returnPacket.order returnPacket.exposed returnPacket.notPrimary
      returnPacket.short returnPacket.activity settings.thread settings.active settings.race
      settings.backend settings.ghost settings.shallow #[] extras outside settings.fuel
      settings.debugOff settings.validationFuel source body identity callee location frameSize
      (congrArg LocalState.value slot0Row) (congrArg LocalState.layout slot0Row)
      (congrArg LocalState.value slot3Row) (congrArg LocalState.value slot4Row)
      (congrArg LocalState.value slot5Row) (congrArg LocalState.layout slot4Row)
      (congrArg LocalState.layout slot5Row) (congrArg LocalState.value slot2Row)
      (congrArg LocalState.layout slot2Row) noClocks returnPlace continuation immediateLocals
      varargs settings.unchecked settings.noGc settings.fixed
  exact ⟨Storage.withCurrent #[] installed after.machine,done,actual,trace,terminal,empty,noErrors,noUB,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.S02WildcardSourceWildcardZeroResult

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSourceWildcardZeroResult.result) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard zero-result dependency {dependency}"
