import duplicate_prefix.CurrentCallEmptyProtocolControl
import duplicate_prefix.S03NonliveEmptyBody
namespace DuplicatePrefix.CurrentCallEmptyNonliveBodyControl
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Interpreter
open RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

private def rank (i : Fin 6) : Nat := if i.val=0 then 4 else i.val-2
private theorem rank_bound (i : Fin 6) : rank i≤4 := by
  unfold rank
  split <;> omega

private def catalog (parent current : BorTag) (room : current.value.toNat+4<2^64) (i : Fin 6) : BorTag :=
  if i.val=1 then parent else ⟨UInt64.ofNat (current.value.toNat+rank i),by
    intro zero
    have value := congrArg UInt64.toNat zero
    have bound : current.value.toNat+rank i<2^64 := by have := rank_bound i;omega
    simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt bound,UInt64.toNat_zero] at value
    have positive := UInt64.lt_iff_toNat_lt.mp (UInt64.pos_iff_ne_zero.mpr current.nonzero)
    omega⟩

private theorem catalog_value (parent current : BorTag) (i : Fin 6)
    (room : current.value.toNat+4<2^64) (other : i.val≠1) :
    (catalog parent current room i).value.toNat=current.value.toNat+rank i := by
  simp only [catalog,other,↓reduceIte,UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by have := rank_bound i;omega)

private theorem catalog_injective (parent current : BorTag)
    (below : parent.value.toNat<current.value.toNat) (room : current.value.toNat+4<2^64) :
    Function.Injective (catalog parent current room) := by
  intro a b equal
  have values := congrArg (fun tag : BorTag => tag.value.toNat) equal
  by_cases ha : a.val=1
  · by_cases hb : b.val=1
    · exact Fin.ext (ha.trans hb.symm)
    · rw [catalog_value parent current b room hb] at values
      simp only [catalog,ha,↓reduceIte] at values
      omega
  · by_cases hb : b.val=1
    · rw [catalog_value parent current a room ha] at values
      simp only [catalog,hb,↓reduceIte] at values
      omega
    · rw [catalog_value parent current a room ha,catalog_value parent current b room hb] at values
      apply Fin.ext
      unfold rank at values
      by_cases za : a.val=0 <;> by_cases zb : b.val=0 <;> simp only [za,zb,↓reduceIte] at values <;> omega

private theorem tag_ext (a b : BorTag) (same : a.value.toNat=b.value.toNat) : a=b := by
  cases a;cases b
  congr
  exact UInt64.toNat_inj.mp same

/-- The existing nonlive helper path consumes the neutral actual copy frame.
No source-family, old image Effect, or Supported certificate is needed. -/
theorem to_return (options : EvalConfigurationCore.Options)
    (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (root : RootFrame)
    (raw : root.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (sourceFrame : FrameState) (boolId : AllocId) (boolTag : BorTag)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker)
    (parent : BorTag) (id : AllocId) (metadataTag : Option BorTag) (base offset count : UInt64)
    (nonzero : base+offset≠0) (countNonzero : count≠0)
    (nonliveMetadata : DuplicatePrefixEmptyReferenceInput.Metadata machine.memory id metadataTag)
    (absent : machine.memory.live.find? (fun row=>row.1==id)=none)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (parentBelow : parent.value.toNat<tracker.global.nextPointerTag.value.toNat)
    (catalogRoom : tracker.global.nextPointerTag.value.toNat+4<2^64)
    (protectorsBelow : ∀ row ∈ tracker.global.protectedTags.entries,
      row.1.value.toNat<tracker.global.nextPointerTag.value.toNat)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (dynamicFuel validityFuel budget : Nat)
    (dynamicEq : options.place.dynamicFuel=dynamicFuel+1) (validityEq : options.limits.validation=validityFuel+1)
    (dispatchFuel : limits.callDispatch=budget+1)
    (tagRoomNext : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615)
    (thread : Miri.Concurrency.ThreadRecord) (activeThread : machine.threads.activeThread?=some thread)
    (topZero : thread.topUserRelevantFrame=some 0) :
    let frame := CurrentCallEmptyProtocolControl.frame root
      (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id parent) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
      sourceFrame count boolId boolTag
    ∃ result : CompilerFrameContext.ActualFrame,
      ∃ finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      ∃ finalTracker : MachineHooks.BorrowState,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] result finalMachine) ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧ result.functionInstance = frame.functionInstance ∧
      result.extra = frame.extra ∧ result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧ result.locals.size = 25 ∧
      result.location = .mir ⟨10,0⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      CopyHelperCleanup.AllImmediate result ∧
      finalMachine.memory = machine.memory ∧
      finalMachine.borrowTracker = some finalTracker ∧ finalTracker.retagMode = tracker.retagMode ∧
      finalTracker.global = {tracker.global with nextPointerTag := finalTracker.global.nextPointerTag} ∧
      finalTracker.global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+2 ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧ finalMachine.threads.fixedScheduling = true ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).gcInterval = 0 ∧
      finalMachine.user.addresses = machine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      finalMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      (∃ finalThread, finalMachine.threads.activeThread? = some finalThread) := by
  dsimp only
  let frame := CurrentCallEmptyProtocolControl.frame root
      (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id parent) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
      sourceFrame count boolId boolTag
  let updated:=(RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
    (Pointer.new (.concrete id parent) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
  have locals:=CurrentCallEmptyProtocolControl.locals root updated sourceFrame count boolId boolTag
  have size : frame.locals.size=25 := (congrArg Array.size locals).trans (PositiveRootInstalledFrame.size _ _ _ _ _ _ _ _)
  have cells (i : Fin 25) := PositiveRootInstalledFrame.slot_option root raw updated count {} boolId boolTag boolId boolTag i
  rw [←locals] at cells
  have slots (i : Fin 25) := Option.some.inj ((Array.getElem?_eq_getElem (show i.val<frame.locals.size by rw [size];exact i.isLt)).symm.trans (cells i))
  have immediate : CopyHelperCleanup.AllImmediate frame := by
    change ∀current∈frame.locals,∀memory,current.value≠.live (.indirect memory)
    rw [locals]
    exact PositiveRootInstalledFrame.immediate _ raw _ _ _ _ _ _ _
  obtain ⟨body,identity,callee,continuation,returnPlace,varargs,clocks,borrow,location⟩:=
    CurrentCallEmptyProtocolControl.metadata root updated sourceFrame count boolId boolTag
  obtain ⟨current,enabled,mode⟩ := model.defaultTracker
  have equal : current=tracker := Option.some.inj (enabled.symm.trans tracked)
  subst current
  have source1 : (frame.locals[1]'(by rw [size];decide)).value=.live (.immediate updated) := by
    simpa [frame] using congrArg LocalState.value (slots ⟨1,by decide⟩)
  have unused : ∀ i (valid:i<frame.locals.size),7≤i→i≤12→frame.locals[i]'valid=⟨.dead,none⟩ := by
    intro i valid low high
    have bound : i<25 := by rw [size] at valid;exact valid
    have cell := slots ⟨i,bound⟩
    simpa [show (14:Nat)≠i by omega,show (13:Nat)≠i by omega,show (6:Nat)≠i by omega,
      show (0:Nat)≠i by omega,show (2:Nat)≠i by omega,show (1:Nat)≠i by omega] using cell
  let tags := catalog parent tracker.global.nextPointerTag catalogRoom
  have distinct : Function.Injective tags := catalog_injective parent tracker.global.nextPointerTag parentBelow catalogRoom
  have rootTag : parent=tags 1 := by simp [tags,catalog]
  have sharedTag : tracker.global.nextPointerTag=tags 2 := by
    apply tag_ext
    rw [catalog_value parent tracker.global.nextPointerTag 2 catalogRoom (by decide)]
    simp [rank]
  have lenTag : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag=tags 3 := by
    apply tag_ext
    rw [catalog_value parent tracker.global.nextPointerTag 3 catalogRoom (by decide)]
    exact (GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag fresh).trans (by rfl)
  dsimp only [updated] at source1
  rw [rootTag] at source1
  exact S03NonliveEmptyBody.to_return options limits remaining span
    (DuplicatePrefixCallModel.sourceComparator options remaining span machine model) model.nullComparator
    model.preciseOff model.implicitOff model.debugOff dynamicFuel validityFuel dynamicEq validityEq frame machine
    tags distinct id metadataTag base offset count nonzero countNonzero nonliveMetadata absent cachedAddress size source1
    (by simpa using congrArg LocalState.layout (slots ⟨1,by decide⟩))
    (by simpa using congrArg LocalState.value (slots ⟨2,by decide⟩))
    (by simpa using congrArg LocalState.layout (slots ⟨2,by decide⟩))
    (by simpa using congrArg LocalState.value (slots ⟨3,by decide⟩))
    (by simpa using congrArg LocalState.layout (slots ⟨3,by decide⟩))
    (by simpa using congrArg LocalState.value (slots ⟨4,by decide⟩))
    (by simpa using congrArg LocalState.value (slots ⟨5,by decide⟩))
    (by simpa using congrArg LocalState.layout (slots ⟨4,by decide⟩))
    (by simpa using congrArg LocalState.layout (slots ⟨5,by decide⟩)) unused (body.trans root.body) (identity.trans root.identity) (callee.trans root.callee) location (clocks.trans root.noClocks) immediate
    tracker tracked mode fresh sharedTag lenTag protectorsBelow model.ghostOff model.shallow model.unchecked model.noGc
    model.fixedScheduler model.metadata (DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ model.metadata origins)
    budget dispatchFuel tagRoomNext model.noDataRace model.noBackend thread activeThread topZero
    (by simpa using congrArg LocalState.value (slots ⟨0,by decide⟩))
    (by simpa using congrArg LocalState.layout (slots ⟨0,by decide⟩))
    (by simpa using congrArg LocalState.value (slots ⟨13,by decide⟩))
    (by simpa using congrArg LocalState.layout (slots ⟨13,by decide⟩))

end
end DuplicatePrefix.CurrentCallEmptyNonliveBodyControl

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyNonliveBodyControl" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty nonlive body dependency {dependency}"
