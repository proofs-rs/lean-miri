import duplicate_prefix.AddInstalledFrame
import duplicate_prefix.AddPushPreserves
import duplicate_prefix.PointerAddComplete
import duplicate_prefix.SuccessfulTrace
namespace DuplicatePrefix.AddRootComplete
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts AddEntry AddCallStep AddUncachedCall
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
 theorem run (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (pointer : Scalar Provenance) (n : UInt64) (valid : 21 < caller.locals.size)
    (live : caller.locals[21].value = .live (.immediate .uninit))
    (uncached : caller.locals[21].layout = none)
    (noClocks : caller.extra.dataRace = none) (noRace : machine.dataRace = none)
    (body : caller.body = RootBody.reflected.body.body) (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance) (trackNone : caller.trackCallerArg = none)
    (location : caller.location = .mir ⟨7,RootCallerLocation.statementCount 7⟩)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (top : thread.topUserRelevantFrame = some frames.size)
    (relevant : caller.extra.userRelevance > 0)
    (budget : Nat) (budgetEq : limits.callDispatch = budget+1)
    (backend : machine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (defaultMode : tracker.retagMode = .Default)
    (id : AllocId) (tag : BorTag) (base offset : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (raw : pointer = Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))))
    (address : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (positive : 0 < n.toNat) (fits : n.toNat < 2^63)
    (bounds : offset.toNat + n.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (valid22 : 22 < caller.locals.size) (valid23 : 23 < caller.locals.size)
    (live22 : caller.locals[22].value = .live (.immediate (.scalar pointer)))
    (cache22 : caller.locals[22].layout = some CopyCompilerFacts.destPointerLayout)
    (live23 : caller.locals[23].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cache23 : caller.locals[23].layout = some RootCompilerFacts.usizeLayout) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let cached := cachedCaller caller valid
    let resultValue := Scalar.fromPointer cfg.access.runtime.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset+n)))
    SuccessfulTrace.Trace cfg limits (Storage.withCurrent frames caller machine)
      (Storage.withCurrent frames
        {PointerAddReturn.writeFrame cached 21 (.scalar resultValue) (by simpa [cached,cachedCaller,LocalPlaces.cachePlaceLayout] using valid)
          with location := .mir ⟨8,0⟩}
        (PointerAddReturn.accountedMachine options remaining span (AddPushPreserves.post options remaining span machine))) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let cached := cachedCaller caller valid
  let next := AddCallStep.accountedMachine options remaining span machine
  let before := Storage.withCurrent frames cached next
  let destination := (LocalPlaces.localRuntimePlace frames.size cached 21 CopyCompilerFacts.destPointerLayout).stackView
  let root := AddEntry.rawRoot before destination (.goto (some 8) .Continue) noRace
  let installed := AddInstalledFrame.installed root pointer n AddEntryFacts.addPreamble (RootCallerLocation.sourceInfo 7).span
  let post := AddPushPreserves.post options remaining span machine
  have first := AddCallStep.step options limits remaining span debug frames caller machine tracker tracked pointer n valid
    .uninit live uncached noClocks noRace body identity callee trackNone location fuel validationFuel ghost shallow
    thread active top relevant budget budgetEq backend unchecked noGc fixed source cmp valid22 valid23 live22 cache22 live23 cache23
  have first' : ExecutionMachine.step cfg limits () (Storage.withCurrent frames caller machine) =
      (Storage.withCurrent (frames.push cached) installed post,.ok true) := first
  have preserved := AddPushPreserves.fields options remaining span machine
  have postTracked : post.borrowTracker = some tracker := preserved.2.1.trans tracked
  have postActive : post.threads.activeThread? = some thread := by rw [show post.threads = machine.threads from preserved.2.2.1];exact active
  have postGhost : post.user.payload.ghost = false := preserved.2.2.2.2.2.1.trans ghost
  have postShallow : post.user.payload.validation = .Shallow := preserved.2.2.2.2.2.2.1.trans shallow
  have postAddress : post.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    rw [show post.user.addresses = machine.user.addresses from preserved.2.2.2.2.1]; exact address
  have postPresent : post.memory.live.find? (fun row => row.1 == id) = some (id,entry) := by rw [show post.memory = machine.memory from preserved.1];exact present
  have postControl := AddPushPreserves.control options remaining span machine
  have postUnchecked : (cfg.terminators.getControl post.user).checkedArithmetic = false := by
    rw [postControl]; exact unchecked
  have postNoGc : (cfg.terminators.getControl post.user).gcInterval = 0 := by rw [postControl]; exact noGc
  have postFixed : post.threads.fixedScheduling = true := by rw [show post.threads = machine.threads from preserved.2.2.1];exact fixed
  have facts := AddInstalledFrame.metadata root pointer n AddEntryFacts.addPreamble (RootCallerLocation.sourceInfo 7).span
  have size := AddInstalledFrame.size root pointer n AddEntryFacts.addPreamble (RootCallerLocation.sourceInfo 7).span
  have rawLocals : root.frame.locals = Array.replicate 5 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := AddEntry.raw_locals before destination (.goto (some 8) .Continue) noRace
  have slot0 := AddInstalledFrame.slot root rawLocals pointer n AddEntryFacts.addPreamble (RootCallerLocation.sourceInfo 7).span ⟨0,by decide⟩
  have slot1 := AddInstalledFrame.slot root rawLocals pointer n AddEntryFacts.addPreamble (RootCallerLocation.sourceInfo 7).span ⟨1,by decide⟩
  have slot2 := AddInstalledFrame.slot root rawLocals pointer n AddEntryFacts.addPreamble (RootCallerLocation.sourceInfo 7).span ⟨2,by decide⟩
  have slot3 := AddInstalledFrame.slot root rawLocals pointer n AddEntryFacts.addPreamble (RootCallerLocation.sourceInfo 7).span ⟨3,by decide⟩
  have slot4 := AddInstalledFrame.slot root rawLocals pointer n AddEntryFacts.addPreamble (RootCallerLocation.sourceInfo 7).span ⟨4,by decide⟩
  simp only [Fin.val_mk,Nat.reduceEqDiff,ite_false,ite_true] at slot0 slot1 slot2 slot3 slot4
  have installedBorrow : installed.extra.borrowTracker = some ({} : FrameState) := by
    rw [AddInstalledFrame.extra]
    simp only [root,AddEntry.rawRoot,AddFrameData.raw,TrackedFrame.raw,CallEntryFacts.freshRoot,
      before,next,Storage.withCurrent,AddCallStep.accountedMachine,PtrMetadataReturn.accountedMachine,SourceControl.accounted,tracked,Option.map_some]
  have validCached : 21 < cached.locals.size := by simpa [cached,cachedCaller,LocalPlaces.cachePlaceLayout] using valid
  have cachedLive : cached.locals[21].value = .live (.immediate .uninit) := by simpa [cached,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self] using live
  have cachedLayout : cached.locals[21].layout = some CopyCompilerFacts.destPointerLayout := by simp [cached,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self]
  obtain ⟨f1,f2,f3,f4,f5,f6,done,s1,s2,s3,s4,s5,s6,s7,s8,doneExtra⟩ := PointerAddComplete.body_returns_offset
    options limits remaining span debug fuel validationFuel frames cached installed post id tag base offset n entry size
    (by rw [slot0]) (by rw [slot0]) (by rw [slot1,raw]) (by rw [slot1]) (by rw [slot2]) (by rw [slot2])
    (by rw [slot3]) (by rw [slot3]) (by rw [slot4]) (by rw [slot4])
    (facts.1.trans root.body) (facts.2.1.trans root.identity) (facts.2.2.1.trans root.callee) facts.2.2.2.2.2.2.2.2 root.noClocks
    tracker postTracked defaultMode postGhost postShallow postAddress postPresent positive fits bounds
    21 validCached cachedLive cachedLayout noClocks (by rw [facts.2.2.2.2.1];rfl) 8 .Continue
    (by rw [facts.2.2.2.1];rfl) (by rw [facts.2.2.2.2.2.1];rfl) {} installedBorrow rfl
    thread postActive postUnchecked postNoGc postFixed
  have tail : SuccessfulTrace.Trace cfg limits (Storage.withCurrent (frames.push cached) installed post)
      (Storage.withCurrent frames
        {PointerAddReturn.writeFrame cached 21 (.scalar (Scalar.fromPointer cfg.access.runtime.base
          (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset+n))))) validCached with location := .mir ⟨8,0⟩}
        (PointerAddReturn.accountedMachine options remaining span post)) := by
    have final := s8
    simp only [top,Option.getD_some,PointerAddReturn.poppedMachine,GenericPopFrame.afterRelevanceAt,Array.size_push,Nat.ne_add_one,ite_false] at final
    exact .next s1 (.next s2 (.next s3 (.next s4 (.next s5 (.next s6 (.next s7 (.next final (.refl _))))))))
  exact .next first' tail
end DuplicatePrefix.AddRootComplete
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.AddRootComplete.run) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved full root add call dependency {dependency}"
