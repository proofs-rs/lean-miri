import duplicate_prefix.GenericAsMutInitializedComplete
import duplicate_prefix.GenericAsMutReturnState
import duplicate_prefix.PositiveRootAddToCopy
import duplicate_prefix.PositiveRootSuccessProfile

namespace DuplicatePrefix.GenericAsMutBodyToCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

set_option autoImplicit false in
/-- Data at the initialized mutable helper. The source call-entry theorem
supplies this state; release, return and pointer-add successes are derived. -/
structure Input where
  options : EvalConfigurationCore.Options
  limits : ExecutionMachine.Limits
  remaining : Nat
  span : PreparedContracts.FixedSpanQuery
  debug : options.place.debugAssertions = false
  fuel : Nat
  validation : options.limits.validation = fuel+1
  dynamicFuel : Nat
  dynamic : options.place.dynamicFuel = dynamicFuel+1
  cmp : ProjectionMetadataFacts.NullComparator
  source : PreparedContracts.SourceComparator
  budget : Nat
  dispatch : limits.callDispatch = budget+1
  caller : CompilerFrameContext.ActualFrame
  initial : CanonicalConfigFacts.RootState
  initialRace : initial.machine.dataRace = none
  parent : Immediate Provenance
  machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  id : AllocId
  tag : BorTag
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  base : UInt64
  offset : UInt64
  len : UInt64
  positive : (0 : UInt64) < len
  nonzero : base+offset ≠ 0
  signedFits : len.toNat < 9223372036854775808
  bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat
  cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩
  present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry)
  tracker : MachineHooks.BorrowState
  tracked : machine.borrowTracker = some tracker
  mode : tracker.retagMode = .Default
  release : GenericAsMutReleasePlan.Input entry.allocation.extra tracker.global.protectedTags tag
  ghost : machine.user.payload.ghost = false
  shallow : machine.user.payload.validation = .Shallow
  race : machine.dataRace = none
  backend : machine.user.payload.payload.user.backend = .none
  valid15 : (15 : MIR.LocalId) < caller.locals.size
  live15 : (caller.locals[15]'valid15).value = .live (.immediate .uninit)
  cached15 : (caller.locals[15]'valid15).layout = some CopyCompilerFacts.destPointerLayout
  clocks : caller.extra.dataRace = none
  metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)).metadata = PreparedReflection.actual.runtime
  notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)).entries.any (·.value.ty == 4) = false
  thread : ThreadRecord
  newRank : UInt8
  oldRank : UInt8
  active : machine.threads.activeThread? = some (PushThread.after thread 1 newRank oldRank)
  top : thread.topUserRelevantFrame = some 0
  unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false
  noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0
  fixed : machine.threads.fixedScheduling = true
  size : caller.locals.size = 25
  body : caller.body = RootBody.reflected.body.body
  identity : caller.bodyIdentity = RootBody.reflected.body.identity
  callee : caller.functionInstance = RootBody.reflected.functionInstance
  track : caller.trackCallerArg = none
  relevant : caller.extra.userRelevance > 0
  immediate : CopyHelperCleanup.AllImmediate caller
  temp16 : Immediate Provenance
  live16 : caller.locals[16]?.map (·.value) = some (.live (.immediate temp16))
  count : UInt64
  countPositive : (0 : UInt64) < count
  within : count ≤ len/2
  slot2 : caller.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  slot13 : caller.locals[13]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩
  unused : ∀ index, 17 ≤ index → index ≤ 24 → caller.locals[index]? = some ⟨.dead,none⟩

noncomputable def pointer (input : Input) : Scalar Provenance :=
  Scalar.fromPointer (PreparedContracts.actualConfig input.options () (input.remaining+1) input.span).access.runtime.base
    (Pointer.new (.concrete input.id input.tag) (Size.ofBytes (input.base+input.offset)))

noncomputable def helper (input : Input) :=
  let rawPointer := Pointer.new (.concrete input.id input.tag) (Size.ofBytes (input.base+input.offset))
  let adjusted := (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig input.options () input.remaining input.span).access.runtime.base
    rawPointer input.len ActualReferenceMetadata.reference).imm
  let destination := (LocalPlaces.localRuntimePlace 0 input.caller 15 CopyCompilerFacts.destPointerLayout).stackView
  GenericAsMutEntry.initialized input.options input.initial destination input.parent adjusted input.id input.tag

noncomputable def memory (input : Input) :=
  StackPopRelease.commitTree input.machine.memory input.id input.entry
    (GenericAsMutReleasePlan.release input.entry.allocation.extra input.tracker.global.protectedTags input.tag).tree

def held (input : Input) :=
  {input.tracker with global := input.tracker.global.endCall (({} : FrameState).addProtector input.id input.tag)}

theorem run (input : Input) :
    let config := PreparedContracts.actualConfig input.options () (input.remaining+1) input.span
    let destinationValue := Scalar.fromPointer config.access.runtime.base
      (Pointer.new (.concrete input.id input.tag) (Size.ofBytes (input.base+input.offset+input.count)))
    ∃ result finalMachine,
      SuccessfulTrace.Trace config input.limits (Storage.withCurrent #[input.caller] (helper input) input.machine)
        (Storage.withCurrent #[] result finalMachine) ∧
      PositiveRootSuccessProfile.FrameShape input.caller result (pointer input) destinationValue input.count ∧
      finalMachine.memory = memory input ∧ finalMachine.borrowTracker = some (held input) ∧
      finalMachine.dataRace = none ∧ finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.user.payload.payload.user.backend = .none ∧ finalMachine.user.addresses = input.machine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = input.machine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.runtime.extras = input.machine.user.payload.payload.user.runtime.extras ∧
      finalMachine.threads.activeThread? = some input.thread ∧ finalMachine.threads.fixedScheduling = true ∧
      (config.terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      (config.terminators.getControl finalMachine.user).gcInterval = 0 := by
  let config := PreparedContracts.actualConfig input.options () (input.remaining+1) input.span
  let helperThread := PushThread.after input.thread 1 input.newRank input.oldRank
  obtain ⟨done,helperTrace,extra⟩ := GenericAsMutInitializedComplete.run input.options input.limits input.remaining input.span
    input.debug input.fuel input.validation input.dynamicFuel input.dynamic input.cmp #[] input.caller input.initial input.initialRace
    input.parent input.machine input.tag input.id input.entry input.base input.offset input.len input.present input.positive input.nonzero
    input.signedFits input.bounds input.cachedAddress input.tracker input.tracked input.mode input.release input.ghost input.shallow
    15 input.valid15 input.live15 input.cached15 input.clocks input.metadata input.notConstructed helperThread input.active
    input.unchecked input.noGc input.fixed
  let a := {AsMutPtrReturn.writeFrame input.caller 15 (.scalar (pointer input)) input.valid15 with location := .mir ⟨7,0⟩}
  let am := GenericAsMutReturnState.machine input.options input.remaining input.span #[] input.caller done input.machine
    (memory input) input.tracker (({} : FrameState).addProtector input.id input.tag) helperThread
  obtain ⟨pm,pt,pr,pf,pa,pg,pv,pty,pb,pe⟩ := GenericAsMutReturnState.fields input.options input.remaining input.span #[] input.caller done
    input.machine (memory input) input.tracker (({} : FrameState).addProtector input.id input.tag) helperThread
  have active := GenericAsMutReturnState.active input.options input.remaining input.span input.caller done input.machine
    (memory input) input.tracker (({} : FrameState).addProtector input.id input.tag) input.thread input.newRank input.oldRank input.active input.top
  have size : a.locals.size = 25 := by simpa only [a,AsMutPtrReturn.writeFrame,Array.size_set] using input.size
  have av (index : Fin 25) : index.val < a.locals.size := by rw [size];exact index.isLt
  have cv (index : Fin 25) : index.val < input.caller.locals.size := by rw [input.size];exact index.isLt
  have other (index : Nat) (different : index ≠ 15) : a.locals[index]? = input.caller.locals[index]? := by
    simp only [a,AsMutPtrReturn.writeFrame,Array.getElem?_set,different,Ne.symm different,↓reduceIte]
  have same (index : Fin 25) (different : index.val ≠ 15) : a.locals[index.val]'(av index) = input.caller.locals[index.val]'(cv index) :=
    Option.some.inj ((Array.getElem?_eq_getElem (av index)).symm.trans ((other index.val different).trans (Array.getElem?_eq_getElem (cv index))))
  have slot15 : a.locals[15]'(av ⟨15,by decide⟩) = ⟨.live (.immediate (.scalar (pointer input))),some CopyCompilerFacts.destPointerLayout⟩ := by
    simp only [a,AsMutPtrReturn.writeFrame,Array.getElem_set_self,input.cached15]
  have slot2 : input.caller.locals[2]'(cv ⟨2,by decide⟩) = ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 input.count)))),some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (cv ⟨2,by decide⟩)).symm.trans input.slot2)
  have live16 : (input.caller.locals[16]'(cv ⟨16,by decide⟩)).value = .live (.immediate input.temp16) := by
    have known := input.live16
    simpa only [Array.getElem?_eq_getElem (cv ⟨16,by decide⟩),Option.map_some,Option.some.injEq] using known
  have all : CopyHelperCleanup.AllImmediate a := by
    apply CopyHelperCleanup.all_immediate_set input.caller 15 _ input.valid15 input.immediate
    intro indirect
    simp
  have unused : ∀ index (valid : index < a.locals.size), 17 ≤ index → index ≤ 24 → a.locals[index]'valid = ⟨.dead,none⟩ := by
    intro index valid lower upper
    apply Option.some.inj
    rw [←Array.getElem?_eq_getElem valid,other index (by omega)]
    exact input.unused index lower upper
  have amUnchecked : (config.terminators.getControl am.user).checkedArithmetic = false := by
    rw [GenericAsMutReturnState.control]
    exact input.unchecked
  have amNoGc : (config.terminators.getControl am.user).gcInterval = 0 := by
    rw [GenericAsMutReturnState.control]
    exact input.noGc
  let updated : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {input.entry with allocation := input.entry.allocation.setExtra (GenericAsMutReleasePlan.release input.entry.allocation.extra input.tracker.global.protectedTags input.tag).tree}
  have present : am.memory.live.find? (fun row => row.1 == input.id) = some (input.id,updated) := by
    rw [pm]
    exact StackPopRelease.lookup_commit_same input.machine.memory input.id input.entry _
  obtain ⟨result,trace,rb,ri,rfn,rex,rrp,rrc,rva,rli,rtrack,rsz,rloc,r17,r18,r19,r21,r24,rkeep,ra⟩ :=
    PositiveRootAddToCopy.executes input.options input.limits input.remaining input.span input.debug input.fuel input.validation #[] a am
      (pointer input) input.count input.temp16 size (by rw [slot15]) (by rw [slot15])
      (by rw [same ⟨16,by decide⟩ (by decide)];exact live16)
      (by rw [same ⟨2,by decide⟩ (by decide),slot2]) (by rw [same ⟨2,by decide⟩ (by decide),slot2]) unused
      input.body input.identity input.callee rfl input.clocks (held input) pt input.mode
      (pg.trans input.ghost) (pv.trans input.shallow) all input.track input.relevant input.thread active input.top input.budget input.dispatch
      (pb.trans input.backend) (pr.trans input.race) amUnchecked amNoGc (pf.trans input.fixed) input.id input.tag input.base input.offset input.len updated rfl
      (by rw [pa];exact input.cachedAddress) present input.countPositive input.within input.bounds input.source input.cmp
  have frame : PositiveRootSuccessProfile.FrameShape input.caller result (pointer input)
      (Scalar.fromPointer config.access.runtime.base (Pointer.new (.concrete input.id input.tag) (Size.ofBytes (input.base+input.offset+input.count)))) input.count := by
    refine ⟨rb,ri,rfn,rex,rrp,rrc,rva,rli,rtrack,rsz,rloc,?_,?_,?_,?_,?_,r17,r18,r19,r21,r24,ra⟩
    · exact (rkeep 0 (Or.inl (by decide))).trans (other 0 (by decide))
    · exact (rkeep 1 (Or.inl (by decide))).trans (other 1 (by decide))
    · exact (rkeep 2 (Or.inl (by decide))).trans (other 2 (by decide))
    · exact (rkeep 13 (Or.inl (by decide))).trans ((other 13 (by decide)).trans input.slot13)
    · exact (rkeep 15 (Or.inl (by decide))).trans ((Array.getElem?_eq_getElem (av ⟨15,by decide⟩)).trans (congrArg some slot15))
  obtain ⟨qm,qt,qth,qr,qa,qg,qv,qb,qe,qty⟩ := AddOutput.preserved input.options input.remaining input.span am
  refine ⟨result,AddOutput.machine input.options input.remaining input.span am,SuccessfulTrace.append helperTrace trace,frame,
    qm.trans pm,qt.trans pt,qr.trans (pr.trans input.race),qg.trans (pg.trans input.ghost),qv.trans (pv.trans input.shallow),
    qb.trans (pb.trans input.backend),qa.trans pa,qty.trans pty,qe.trans pe,?_,?_,?_,?_⟩
  · rw [qth]
    exact active
  · rw [qth]
    exact pf.trans input.fixed
  · rw [AddOutput.control]
    exact amUnchecked
  · rw [AddOutput.control]
    exact amNoGc

end DuplicatePrefix.GenericAsMutBodyToCopy
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.GenericAsMutBodyToCopy.run) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved generic asmut body-to-copy dependency {dependency}"
