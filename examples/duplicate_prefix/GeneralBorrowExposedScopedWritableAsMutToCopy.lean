import duplicate_prefix.GeneralBorrowExposedScopedWritableAsMutCallReturnReady
import duplicate_prefix.PositiveRootAddToCopy
import duplicate_prefix.PositiveRootSuccessProfile
import duplicate_prefix.CopyRootEntry
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableAsMutToCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open GeneralBorrowExposedScopedWritableAsMutCallInput GeneralBorrowExposedScopedWritableAsMutCallReturn
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
set_option autoImplicit false in
/-- Additional MIR caller metadata at the actual as_mut_ptr call site. All
permissions and physical helper data are the underlying source call Input. -/
structure Input extends GeneralBorrowExposedScopedWritableAsMutCallInput.Input where
  size : caller.locals.size=25
  trackNone : caller.trackCallerArg=none
  relevant : caller.extra.userRelevance>0
  immediate : CopyHelperCleanup.AllImmediate caller
  count : UInt64
  countPositive : (0:UInt64)<count
  within : count≤len/2
  slot2 : caller.locals[2]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  slot13 : caller.locals[13]?=some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩
  unused : ∀ index,17≤index→index≤24→caller.locals[index]?=some ⟨.dead,none⟩

def scalar (s : Input) : Scalar Provenance:=Scalar.fromPointer
  (ActualReferenceContext.config s.options (s.remaining+1) s.span).access.runtime.base (pointer s.toInput)
def destinationScalar (s : Input) : Scalar Provenance:=Scalar.fromPointer
  (ActualReferenceContext.config s.options (s.remaining+1) s.span).access.runtime.base
  (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset+s.count)))

theorem executes (s : Input) :
    let cfg:=ActualReferenceContext.config s.options (s.remaining+1) s.span
    let ended:=(held s.toInput).global.endCall (({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag)
    let anchor:=GeneralBorrowFreshMetadataChildMutable.index s.data.input
    ∃ root post,
      SuccessfulTrace.Trace cfg s.limits (Storage.withCurrent #[] s.caller s.machine) (Storage.withCurrent #[] root post) ∧
      PositiveRootSuccessProfile.FrameShape s.caller root (scalar s) (destinationScalar s) s.count ∧
      post.memory=RetagEntry.updatedMemory s.machine.memory s.id s.entry (released s.toInput) ∧
      post.borrowTracker=some {held s.toInput with global:=ended} ∧
      GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.machine post ∧
      (∃ copy : CopyRootEntry.Input s.options s.limits s.remaining s.span #[] root post (scalar s) (destinationScalar s) s.count, True) ∧
      ∃ context : GeneralBorrowExposedKnownRootRangeData.Context (released s.toInput) anchor s.selected s.head s.tail,
        GeneralRangeMapOrigins.OwnedOn (fun location=>
          Nonempty (GeneralBorrowExposedScopedWritableReadData.Data (released s.toInput) location ended.protectedTags anchor s.selected s.head s.tail
            (fun position=>s.data.resources.component.support position ∨ position=anchor.toNat) (fun _=>true)) ∧
          Nonempty (GeneralBorrowExposedKnownRootRangeData.Data (released s.toInput) location ended.protectedTags anchor s.selected s.head s.tail .Write) ∧
          Nonempty (GeneralBorrowExposedScopedLeafWriteReadClosed.Data (released s.toInput) location ended.protectedTags anchor s.selected s.head s.tail))
          s.offset (s.offset+s.len) (released s.toInput).locations ∧
        (released s.toInput).locations.WellFormed ∧ (released s.toInput).locations.size=s.entry.allocation.extra.locations.size := by
  obtain ⟨a,am,helperTrace,frameEq,memoryEq,trackedEq,runtime,context,owned,well,capacity⟩:=
    GeneralBorrowExposedScopedWritableAsMutCallReturnReady.executes s.toInput
  let tracker:={held s.toInput with global:=(held s.toInput).global.endCall (({}:FrameState).addProtector s.id s.tracker.global.nextPointerTag)}
  have size : a.locals.size=25 := by rw [frameEq];simpa [caller,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,AsMutPtrReturn.writeFrame] using s.size
  have av (index : Fin 25) : index.val<a.locals.size:=by rw [size];exact index.isLt
  have cv (index : Fin 25) : index.val<s.caller.locals.size:=by rw [s.size];exact index.isLt
  have other (index : Nat) (different : index≠15) : a.locals[index]?=s.caller.locals[index]? := by
    rw [frameEq]
    simp [caller,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,AsMutPtrReturn.writeFrame,Array.getElem?_set,Ne.symm different,different]
  have same (index : Fin 25) (different : index.val≠15) : a.locals[index.val]'(av index)=s.caller.locals[index.val]'(cv index) :=
    Option.some.inj ((Array.getElem?_eq_getElem (av index)).symm.trans ((other index.val different).trans (Array.getElem?_eq_getElem (cv index))))
  have slot15 : a.locals[15]'(av ⟨15,by decide⟩)=⟨.live (.immediate (.scalar (scalar s))),some CopyCompilerFacts.destPointerLayout⟩ := by
    simp [frameEq,caller,scalar,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,AsMutPtrReturn.writeFrame]
  have slot2 : s.caller.locals[2]'(cv ⟨2,by decide⟩)=⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 s.count)))),some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (cv ⟨2,by decide⟩)).symm.trans s.slot2)
  have helperValid : (15:MIR.LocalId)<(caller s.toInput).locals.size := by
    simpa [caller,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using s.valid15
  have all : CopyHelperCleanup.AllImmediate a := by
    rw [frameEq]
    apply CopyHelperCleanup.all_immediate_set (caller s.toInput) 15 _ helperValid
      (CopyHelperCleanup.all_immediate_cache s.caller 15 CopyCompilerFacts.destPointerLayout s.valid15 s.immediate)
    intro indirect;simp
  have unused : ∀ index (valid:index<a.locals.size),17≤index→index≤24→a.locals[index]'valid=⟨.dead,none⟩ := by
    intro index valid lower upper
    apply Option.some.inj
    rw [←Array.getElem?_eq_getElem valid,other index (by omega)]
    exact s.unused index lower upper
  have body : a.body=s.caller.body := by rw [frameEq];rfl
  have identity : a.bodyIdentity=s.caller.bodyIdentity := by rw [frameEq];rfl
  have callee : a.functionInstance=s.caller.functionInstance := by rw [frameEq];rfl
  have extra : a.extra=s.caller.extra := by rw [frameEq];rfl
  have location : a.location=.mir ⟨7,0⟩ := by rw [frameEq]
  have tracked : am.borrowTracker=some tracker:=trackedEq
  obtain ⟨thread,active,top⟩:=runtime.active
  let buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind:={s.entry with allocation:=s.entry.allocation.setExtra (released s.toInput)}
  have present : am.memory.live.find? (fun row=>row.1==s.id)=some (s.id,buffer) := by rw [memoryEq];exact MemoryCopyBridge.live_lookup_replaced _ s.id _
  obtain ⟨result,addTrace,rb,ri,rfn,rex,rrp,rrc,rva,rli,rtrack,rsz,rloc,r17,r18,r19,r21,r24,rkeep,ra⟩:=
    PositiveRootAddToCopy.executes s.options s.limits s.remaining s.span s.debug s.fuel s.validation #[] a am
      (scalar s) s.count (parent s.toInput) size (by rw [slot15]) (by rw [slot15])
      (by rw [same ⟨16,by decide⟩ (by decide)];exact s.live16)
      (by rw [same ⟨2,by decide⟩ (by decide),slot2]) (by rw [same ⟨2,by decide⟩ (by decide),slot2]) unused
      (body.trans s.body) (identity.trans s.identity) (callee.trans s.callee) location (by rw [extra];exact s.clocks)
      tracker tracked s.mode runtime.ghost runtime.shallow all (by rw [frameEq];exact s.trackNone) (by rw [extra];exact s.relevant)
      thread active top s.budget s.dispatch runtime.backend runtime.race runtime.unchecked runtime.noGc runtime.fixed
      s.id s.tracker.global.nextPointerTag s.base s.offset s.len buffer rfl
      (by rw [runtime.addresses];exact s.cachedAddress) present s.countPositive s.within s.bounds s.source s.cmp
  let post:=AddOutput.machine s.options s.remaining s.span am
  obtain ⟨pm,pt,pth,pr,pa,pg,pv,pb,pe,pty⟩:=AddOutput.preserved s.options s.remaining s.span am
  have profile : PositiveRootSuccessProfile.FrameShape s.caller result (scalar s) (destinationScalar s) s.count := by
    refine ⟨rb.trans body,ri.trans identity,rfn.trans callee,rex.trans extra,?_,?_,?_,?_,?_,rsz,rloc,?_,?_,?_,?_,?_,r17,r18,r19,r21,r24,ra⟩
    · rw [rrp,frameEq];rfl
    · rw [rrc,frameEq];rfl
    · rw [rva,frameEq];rfl
    · rw [rli,frameEq];rfl
    · rw [rtrack,frameEq];rfl
    · exact (rkeep 0 (Or.inl (by decide))).trans (other 0 (by decide))
    · exact (rkeep 1 (Or.inl (by decide))).trans (other 1 (by decide))
    · exact (rkeep 2 (Or.inl (by decide))).trans (other 2 (by decide))
    · exact (rkeep 13 (Or.inl (by decide))).trans ((other 13 (by decide)).trans s.slot13)
    · exact (rkeep 15 (Or.inl (by decide))).trans ((Array.getElem?_eq_getElem (av ⟨15,by decide⟩)).trans (congrArg some slot15))
  have postRuntime : GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.machine post := by
    refine ⟨pg.trans runtime.ghost,pv.trans runtime.shallow,pr.trans runtime.race,pa.trans runtime.addresses,
      pty.trans runtime.types,pe.trans runtime.extras,pb.trans runtime.backend,?_,?_,?_,?_⟩
    · rw [AddOutput.control];exact runtime.unchecked
    · rw [AddOutput.control];exact runtime.noGc
    · rw [pth];exact runtime.fixed
    · exact ⟨thread,by rw [pth];exact active,top⟩
  have cell (index : Fin 25) {row : LocalState Provenance LocalLayout} (known : result.locals[index.val]?=some row) :
      result.locals[index.val]'(by rw [rsz];exact index.isLt)=row :=
    Option.some.inj ((Array.getElem?_eq_getElem (by rw [rsz];exact index.isLt)).symm.trans known)
  let copy : CopyRootEntry.Input s.options s.limits s.remaining s.span #[] result post (scalar s) (destinationScalar s) s.count := {
    debug:=s.debug,tracker:=tracker,tracked:=pt.trans tracked,valid:=by rw [rsz];decide,old:=.uninit,
    live:=by rw [cell ⟨18,by decide⟩ r18],uncached:=by rw [cell ⟨18,by decide⟩ r18],noClocks:=by rw [profile.extra];exact s.clocks,
    noRace:=postRuntime.race,body:=profile.body.trans s.body,identity:=profile.identity.trans s.identity,callee:=profile.callee.trans s.callee,
    trackNone:=profile.trackedCaller.trans s.trackNone,location:=by simpa only [show RootCallerLocation.statementCount 8=4 by with_unfolding_all rfl] using rloc,
    fuel:=s.fuel,validationFuel:=s.validation,ghost:=postRuntime.ghost,shallow:=postRuntime.shallow,
    thread:=thread,active:=by rw [pth];exact active,top:=top,relevant:=by rw [profile.extra];exact s.relevant,
    budget:=s.budget,budgetEq:=s.dispatch,backend:=postRuntime.backend,unchecked:=postRuntime.unchecked,noGc:=postRuntime.noGc,fixed:=postRuntime.fixed,
    source:=s.source,cmp:=s.cmp,valid19:=by rw [rsz];decide,valid21:=by rw [rsz];decide,valid24:=by rw [rsz];decide,
    live19:=by rw [cell ⟨19,by decide⟩ r19],cache19:=by rw [cell ⟨19,by decide⟩ r19],
    live21:=by rw [cell ⟨21,by decide⟩ r21];rfl,cache21:=by rw [cell ⟨21,by decide⟩ r21],
    live24:=by rw [cell ⟨24,by decide⟩ r24],cache24:=by rw [cell ⟨24,by decide⟩ r24] }
  exact ⟨result,post,SuccessfulTrace.append helperTrace addTrace,profile,pm.trans memoryEq,pt.trans trackedEq,postRuntime,⟨copy,True.intro⟩,context,owned,well,capacity⟩
end
end DuplicatePrefix.GeneralBorrowExposedScopedWritableAsMutToCopy
