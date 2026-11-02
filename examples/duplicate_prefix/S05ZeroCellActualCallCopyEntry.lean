import duplicate_prefix.S05ZeroCellActualCallAsMutReturn
import duplicate_prefix.S05ZeroCellActualCallRepaired
import duplicate_prefix.PositiveRootAddToCopy
import duplicate_prefix.CopyRootEntry
import duplicate_prefix.RootThreadCache

/-! Source execution from the returned raw pointer through pointer arithmetic
and the actual copy-call entry. No borrowing operation is replaced. -/
namespace DuplicatePrefix.S05ZeroCellActualCallCopyEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext S05ZeroCellActualCallParameters S05ZeroCellJointPacket
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- The popped helper restores the root's cached index even when its own
relevance rank had temporarily replaced that index. -/
theorem popped_root_active
    (caller done : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (bounded : ∀ index,thread.topUserRelevantFrame = some index → index < 2) :
    ∃ result,
      (AsMutPtrReturn.poppedMachine #[] caller done machine
        (thread.topUserRelevantFrame.getD 1)).threads.activeThread? = some result ∧
      result.topUserRelevantFrame = some 0 := by
  unfold AsMutPtrReturn.poppedMachine
  unfold GenericPopFrame.afterRelevanceAt
  split
  · refine ⟨_,MetadataOutputFacts.relevance_active #[caller] done machine thread active,?_⟩
    exact RootThreadCache.compute_pair caller done
  · rename_i different
    cases cached : thread.topUserRelevantFrame with
    | none => simp [cached] at different
    | some index =>
      have small := bounded index cached
      have zero : index = 0 := by simp only [cached,Option.getD_some,Array.size_push,Array.size_empty] at different;omega
      exact ⟨thread,active,by simpa [zero] using cached⟩

/-- Shared-reference preparation updates only the source allocation; the
actual initialized return slot is retained byte-for-byte. -/
theorem shared_destination (span : PreparedContracts.FixedSpanQuery) (updated : Allocation Provenance BorrowTree) :
    (S05ZeroCellActualCallSharedStmt.postMachine span updated).memory.live.find? (fun row => row.1 == destinationId) =
      some (destinationId,⟨destinationEntry.kind,updated⟩) := by
  unfold S05ZeroCellActualCallSharedStmt.postMachine
  apply StackPopRelease.lookup_commit_other _ sourceId destinationId _ _ _ distinct_ids.symm
  unfold S05ZeroCellActualCallSharedStmt.current
  rw [(RootZeroInvocationState.tick_fields options remaining span (S05ZeroCellActualCallInit.installed span updated).machine).1]
  exact S05ZeroCellActualCallInit.installed_destination span updated

/-- Present physical and local data at block seven suffice for its actual
pointer-add and copy-call setup. All helper operations occur in the trace. -/
theorem from_block_seven (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator) (source : PreparedContracts.SourceComparator)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (size : frame.locals.size = 25)
    (slot15 : frame.locals[15]? = some ⟨.live (.immediate (.scalar (S05ZeroCellActualCallAsMutReturn.rawResult span))),some CopyCompilerFacts.destPointerLayout⟩)
    (temp16 : Immediate Provenance)
    (slot16 : frame.locals[16]?.map (·.value) = some (.live (.immediate temp16)))
    (slot2 : frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 1)))),some RootCompilerFacts.usizeLayout⟩)
    (unused : ∀ index,17 ≤ index → index ≤ 24 → frame.locals[index]? = some ⟨.dead,none⟩)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨7,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracked : machine.borrowTracker = some S05ZeroCellActualCallRepaired.copyTracker)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (immediate : CopyHelperCleanup.AllImmediate frame)
    (trackNone : frame.trackCallerArg = none)
    (relevant : frame.extra.userRelevance > 0)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (top : thread.topUserRelevantFrame = some 0)
    (backend : machine.user.payload.payload.user.backend = .none)
    (race : machine.dataRace = none)
    (unchecked : ((config options (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((config options (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == sourceId) = some ⟨sourceId,4096⟩)
    (present : machine.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,S05ZeroCellActualCallRepaired.copyEntry)) :
    let destination := Scalar.fromPointer (config options (remaining+1) span).access.runtime.base
      (Pointer.new (Provenance.concrete sourceId S05ZeroCellActualCallRepaired.PureTree.tag) (Size.ofBytes 4097))
    ∃ caller, ∃ _entry : CopyRootEntry.Input options limits remaining span #[] caller
        (AddOutput.machine options remaining span machine)
        (S05ZeroCellActualCallAsMutReturn.rawResult span) destination 1,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine)
        (Storage.withCurrent #[] caller (AddOutput.machine options remaining span machine)) ∧
      caller.body = frame.body ∧ caller.bodyIdentity = frame.bodyIdentity ∧
      caller.functionInstance = frame.functionInstance ∧ caller.extra = frame.extra ∧
      caller.returnPlace = frame.returnPlace ∧ caller.returnContinuation = frame.returnContinuation ∧
      caller.vaList = frame.vaList ∧ caller.localsIdentity = frame.localsIdentity ∧
      caller.trackCallerArg = frame.trackCallerArg ∧ caller.locals.size = 25 ∧
      caller.locals[17]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      (∀ index,index < 16 ∨ 24 < index → caller.locals[index]? = frame.locals[index]?) ∧
      CopyHelperCleanup.AllImmediate caller := by
  let pointer := S05ZeroCellActualCallAsMutReturn.rawResult span
  let destination := Scalar.fromPointer (config options (remaining+1) span).access.runtime.base
    (Pointer.new (Provenance.concrete sourceId S05ZeroCellActualCallRepaired.PureTree.tag) (Size.ofBytes 4097))
  have v (index : Fin 25) : index.val < frame.locals.size := by rw [size];exact index.isLt
  have cell {index : Nat} (valid : index < frame.locals.size) {row : LocalState Provenance LocalLayout}
      (known : frame.locals[index]? = some row) : frame.locals[index]'valid = row :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans known)
  have row15 := cell (v ⟨15,by decide⟩) slot15
  have row2 := cell (v ⟨2,by decide⟩) slot2
  have live16 : (frame.locals[16]'(v ⟨16,by decide⟩)).value = .live (.immediate temp16) := by
    simpa only [Array.getElem?_eq_getElem (v ⟨16,by decide⟩),Option.map_some,Option.some.injEq] using slot16
  have mode : S05ZeroCellActualCallRepaired.copyTracker.retagMode = .Default := rfl
  obtain ⟨caller,trace,rb,ri,rfn,rex,rrp,rrc,rva,rli,rtrack,rsz,rloc,r17,r18,r19,r21,r24,rkeep,ra⟩ :=
    PositiveRootAddToCopy.executes options limits remaining span rfl remaining rfl #[] frame machine pointer 1 temp16
      size (by rw [row15]) (by rw [row15]) live16 (by rw [row2]) (by rw [row2])
      (by intro index valid lower upper;exact Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans (unused index lower upper)))
      body identity callee location noClocks S05ZeroCellActualCallRepaired.copyTracker tracked mode ghost shallow immediate
      trackNone relevant thread active top remaining rfl backend race unchecked noGc fixed
      sourceId S05ZeroCellActualCallRepaired.PureTree.tag 4096 0 2 S05ZeroCellActualCallRepaired.copyEntry
      rfl cached present (by decide) (by decide) (by change 0+2 ≤ 2;decide) source cmp
  have fields := AddOutput.preserved options remaining span machine
  have cv (index : Fin 25) : index.val < caller.locals.size := by rw [rsz];exact index.isLt
  have found {index : Nat} (valid : index < caller.locals.size) {row : LocalState Provenance LocalLayout}
      (known : caller.locals[index]? = some row) : caller.locals[index]'valid = row :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans known)
  have c18 := found (cv ⟨18,by decide⟩) r18
  have c19 := found (cv ⟨19,by decide⟩) r19
  have c21 := found (cv ⟨21,by decide⟩) r21
  have c24 := found (cv ⟨24,by decide⟩) r24
  let entry : CopyRootEntry.Input options limits remaining span #[] caller
      (AddOutput.machine options remaining span machine) pointer destination 1 := {
    debug := rfl,tracker := S05ZeroCellActualCallRepaired.copyTracker,tracked := fields.2.1.trans tracked
    valid := cv ⟨18,by decide⟩,old := .uninit,live := by rw [c18],uncached := by rw [c18]
    noClocks := by rw [rex];exact noClocks
    noRace := fields.2.2.2.1.trans race,body := rb.trans body,identity := ri.trans identity,callee := rfn.trans callee
    trackNone := rtrack.trans trackNone,location := rloc,fuel := remaining,validationFuel := rfl
    ghost := fields.2.2.2.2.2.1.trans ghost,shallow := fields.2.2.2.2.2.2.1.trans shallow
    thread := thread,active := by rw [fields.2.2.1];exact active
    top := top,relevant := by rw [rex];exact relevant
    budget := remaining,budgetEq := rfl,backend := fields.2.2.2.2.2.2.2.1.trans backend
    unchecked := by rw [AddOutput.control];exact unchecked
    noGc := by rw [AddOutput.control];exact noGc
    fixed := by rw [fields.2.2.1];exact fixed
    source := source,cmp := cmp,valid19 := cv ⟨19,by decide⟩,valid21 := cv ⟨21,by decide⟩,valid24 := cv ⟨24,by decide⟩
    live19 := by rw [c19],cache19 := by rw [c19],live21 := by simpa only [destination,ActualReferenceContext.config,UInt64.add_zero,show (4096 : UInt64)+1=4097 from rfl] using congrArg LocalState.value c21
    cache21 := by rw [c21],live24 := by rw [c24],cache24 := by rw [c24] }
  exact ⟨caller,entry,trace,rb,ri,rfn,rex,rrp,rrc,rva,rli,rtrack,rsz,r17,rkeep,ra⟩

end
end DuplicatePrefix.S05ZeroCellActualCallCopyEntry
