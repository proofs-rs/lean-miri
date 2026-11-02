import duplicate_prefix.GeneralBorrowRawRootAcceptedCompleteLedger
import duplicate_prefix.GeneralBorrowRawRootInitialSlot
import duplicate_prefix.GeneralBorrowRawRootInitialNode
import duplicate_prefix.GeneralBorrowRawDefaultFullTrueObserved
import duplicate_prefix.GeneralBorrowRawSliceBytes
namespace DuplicatePrefix.GeneralBorrowRawRootAcceptedObserved
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
abbrev Initial := GeneralBorrowRawRootZeroEntry.Initial
/-- Accepted branch from ORIGINAL call-time data and count-independent source
bytes. Every intermediate frame, graph, owner, byte-prefix, slot and control fact
is obtained internally from actual initialization/shared/len/mutable/Copy/return. -/
theorem invoke (s : Initial) (n : UInt64) (positiveCount : n ≠ 0) (within : n ≤ s.len/2)
    (preciseOff : s.options.retag.preciseInteriorMut = false)
    (implicitOff : s.options.retag.implicitWrites = false)
    (budget : Nat) (dispatch : s.limits.callDispatch = budget+1)
    (nodeMargin : s.entry.allocation.extra.nodes.size+5 < 65536)
    (tagMargin : s.tracker.global.nextPointerTag.value.toNat+5 < 18446744073709551615)
    (bytes : GeneralBorrowRawSliceBytes.Data s.entry.allocation s.offset s.len)
    (bufferExtras : s.before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == s.id) = some (s.id,⟨none,#[]⟩))
    (statementFuel : s.limits.validation = s.validityFuel+1) :
    ∃ (entryFrame : CompilerFrameContext.ActualFrame)
      (initial : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (physical : GeneralBorrowRawRootBoolReturn.Input),
      GeneralBorrowRawRootPositivePrefix.ActualCall s n entryFrame initial ∧
      physical.value = true ∧ physical.release.slotId = s.slotId ∧ GeneralBorrowRawRootBoolReturn.Result physical ∧
      ∃ updated,
        let terminal := CanonicalCopy.replaceAllocation (GeneralBorrowRawRootBoolReturn.popped physical) physical.release.slotId physical.release.slot.kind updated
        SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits (Storage.withCurrent #[] entryFrame initial) terminal ∧
        ExecutionMachine.step (config s.options (s.remaining+1) s.span) s.limits () terminal = (terminal,.ok false) ∧
        CallSafety.NoUBBeforeReturn ⟨config s.options (s.remaining+1) s.span,s.limits,fun _ _ => True⟩ 1 (Storage.withCurrent #[] entryFrame initial) ∧
        GeneralBorrowRawReturnedBytes.Encoded physical.context updated true := by
  obtain ⟨entryFrame,frame,initial,machine,call,entryEq,prefixTrace,frameFacts,⟨heap⟩⟩ :=
    GeneralBorrowRawRootAcceptedCompleteLedger.executes s n positiveCount within preciseOff implicitOff budget dispatch (by omega) (by omega)
  have physicalFrame := GeneralBorrowRawRootAcceptedCompleteLedger.physical s n entryFrame frame entryEq frameFacts
  have initialResources := GeneralBorrowRawRootPrefixResources.of_call s n entryFrame initial call
  obtain ⟨slot⟩ := GeneralBorrowRawRootInitialSlot.of_call s n entryFrame initial call
  obtain ⟨anchor,oldNode,lookup,oldPresent,oldTag,oldHidden⟩ := GeneralBorrowRawRootInitialNode.exists_node s
  have anchorEq : anchor = heap.observer := Option.some.inj (lookup.symm.trans heap.originalTagged)
  subst anchor
  obtain ⟨node,present,tag,parent,hidden,currentLookup⟩ := heap.graph.oldNodes heap.observer oldNode oldPresent
  obtain ⟨owner⟩ := heap.original
  obtain ⟨thread,active,top⟩ := heap.runtime.active
  have growth : heap.tree.nodes.size ≤ s.entry.allocation.extra.nodes.size+3 := by
    have first := initialResources.growth
    have last := heap.graph.growth
    omega
  have counter : heap.tracker.global.nextPointerTag.value.toNat = s.tracker.global.nextPointerTag.value.toNat+4 := by
    have first := GenericFunctionEntryNumerics.successor_value s.tracker.global.nextPointerTag s.fresh
    have second := GenericFunctionEntryNumerics.successor_value (next s.tracker s.fresh).global.nextPointerTag s.slotFresh
    have last := heap.graph.tagCounter
    change (next s.tracker s.fresh).global.nextPointerTag.value.toNat = s.tracker.global.nextPointerTag.value.toNat+1 at first
    change (held s.tracker s.fresh s.slotFresh).global.nextPointerTag.value.toNat = (next s.tracker s.fresh).global.nextPointerTag.value.toNat+1 at second
    omega
  have fresh : heap.tracker.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change heap.tracker.global.nextPointerTag.value.toNat < 18446744073709551615
    omega
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {s.entry with allocation:=s.entry.allocation.setExtra heap.tree}
  let raw : GeneralBorrowRawDefault.Input heap.tree heap.tracker.global := {
    parentTag:=s.tracker.global.nextPointerTag,parent:=heap.observer,selected:=s.raw.selected,maximum:=s.raw.maximum,
    offset:=s.offset,len:=s.len,tagged:=by rw [←oldTag];exact currentLookup,
    positive:=owner,distinct:=heap.graph.distinct,order:=heap.graph.order,short:=heap.graph.short,
    nodeRoom:=by have h:=heap.graph.short;omega,tagRoom:=fresh}
  have bufferPresent : machine.memory.live.find? (fun row => row.1 == s.id) = some (s.id,entry) := by
    rw [heap.memory]
    exact StackPopRelease.lookup_commit_same initial.memory s.id s.entry heap.tree
  have slotPresent : machine.memory.live.find? (fun row => row.1 == s.slotId) = some (s.slotId,slot.slot) := by
    rw [heap.memory]
    exact StackPopRelease.lookup_commit_other initial.memory s.id s.slotId s.entry slot.slot heap.tree s.separate slot.present
  have valid (i : Fin 25) : i.val < frame.locals.size := by rw [frameFacts.size];exact i.isLt
  have cell (i : Fin 25) (row : LocalState Provenance LocalLayout) (present : frame.locals[i.val]? = some row) : frame.locals[i.val]'(valid i) = row :=
    Option.some.inj ((Array.getElem?_eq_getElem (valid i)).symm.trans present)
  have sourceCell := cell ⟨1,by decide⟩ _ physicalFrame.source
  have destCell := cell ⟨15,by decide⟩ _ frameFacts.temp15
  have tempCell := cell ⟨16,by decide⟩ _ frameFacts.temp16
  let ret : GeneralBorrowRawTrueReturnData.Data s.options s.remaining s.span frame machine heap.tracker s.id entry s.tracker.global.nextPointerTag raw.parent := {
    context:=s.writeContext,validationContext:=s.validationContext,accessEq:=s.accessEq,validationWidth:=s.validationWidth,
    validationRuntimeSize:=s.validationRuntimeSize,sameRuntime:=s.sameRuntime,width:=s.width,runtimeWidth:=s.runtimeWidth,runtimeSize:=s.runtimeSize,outerAccessEq:=s.outerAccessEq,
    sourceNode:=node,sourcePresent:=present,sourceTag:=tag.trans oldTag,sourceHidden:=hidden.trans oldHidden,
    continuation:=physicalFrame.continuation,varargs:=physicalFrame.varargs,slotId:=s.slotId,separate:=s.separate,slot:=slot.slot,slotBefore:=slotPresent,
    slotRoot:=s.slotRoot,slotChild:=GeneralBorrowRawRootInitialSlot.slotTag s,slotTree:=slot.tree,
    slotRootFree:=by rw [heap.graph.protections];exact slot.rootFree,
    slotChildHeld:=by rw [heap.graph.protections];exact slot.childHeld,
    slotDistinct:=slot.distinct,frameTracked:=physicalFrame.tracked,slotSize:=slot.size,slotStorage:=slot.storage,slotMask:=slot.mask,
    slotProvenance:=slot.provenance,slotMutable:=slot.mutable,place:=s.place,layout:=s.layout,slotBase:=s.slotBase,slotPointer:=s.slotPointer,
    aligned:=s.aligned,fits:=s.slotFits,cached:=by rw [heap.runtime.addresses];exact s.slotCached,
    extras:=by change machine.user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [heap.runtime.extras];exact s.extras,
    destination:=by rw [physicalFrame.destination];rfl }
  have byteFacts := (bytes.set_extra heap.tree).for_count n (UInt64.pos_iff_ne_zero.mpr positiveCount) within
  obtain ⟨physical,value,slotId,result,updated,suffixTrace,terminal,safe,encoded⟩ :=
    GeneralBorrowRawDefaultFullTrueObserved.invoke s.options s.limits s.remaining s.span s.ctx s.debugOff s.cmp s.dynamicFuel s.validityFuel
      s.fuelEq s.validationEq s.id entry s.base s.offset s.len s.tracker.global.nextPointerTag s.positive s.nonzero s.signedFits s.bounds
      frame machine heap.tracker heap.tracked heap.mode fresh heap.formed raw rfl rfl rfl
      (heap.graph.capacity.trans (initialResources.capacity.trans s.capacity)) (valid ⟨15,by decide⟩)
      (congrArg LocalState.value destCell) (congrArg LocalState.layout destCell) physicalFrame.clocks heap.runtime.ghost heap.runtime.shallow
      (by rw [heap.runtime.addresses];exact s.cachedAddress) bufferPresent heap.runtime.race
      (by change machine.user.payload.payload.user.types.metadata = _;rw [heap.runtime.types];exact s.metadata)
      (by change machine.user.payload.payload.user.types.entries.any _ = _;rw [heap.runtime.types];exact s.notConstructed)
      thread active (by change heap.tree.nodes.size+2 < 65536;omega) (by omega) preciseOff implicitOff s.source budget dispatch heap.runtime.backend heap.runtime.unchecked heap.runtime.noGc heap.runtime.fixed top
      frameFacts.size frameFacts.body frameFacts.identity frameFacts.callee physicalFrame.track physicalFrame.relevant frameFacts.immediate frameFacts.location
      (valid ⟨16,by decide⟩) (congrArg LocalState.value tempCell) (congrArg LocalState.layout tempCell) (valid ⟨1,by decide⟩)
      (by simpa only [GeneralBorrowRawRootPrefixFrame.sourceValue,ActualReferenceContext.config,CanonicalConfigFacts.actual_access_runtime] using congrArg LocalState.value sourceCell)
      (congrArg LocalState.layout sourceCell) n byteFacts.positive within physicalFrame.count frameFacts.flag physicalFrame.high
      heap.originalActivity frameFacts.zero statementFuel byteFacts.storage byteFacts.maskValid byteFacts.maskLen byteFacts.initialized byteFacts.provenance byteFacts.storageFits byteFacts.mutable
      (by rw [heap.runtime.extras];exact bufferExtras) (byteFacts.bounded s.options s.remaining s.span) ret
  have fullTrace := SuccessfulTrace.append prefixTrace suffixTrace
  let terminalState := CanonicalCopy.replaceAllocation (GeneralBorrowRawRootBoolReturn.popped physical) physical.release.slotId physical.release.slot.kind updated
  have entryCall : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] entryFrame initial) := by simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent]
  have past : CallSafety.pastCallBoundary 1 terminalState := by change (0:Nat)<1;decide
  have wholeSafe := SuccessfulTrace.no_ub ⟨config s.options (s.remaining+1) s.span,s.limits,fun _ _ => True⟩ 1 _ terminalState entryCall fullTrace past
  exact ⟨entryFrame,initial,physical,call,value,slotId,result,updated,fullTrace,terminal,wholeSafe,encoded⟩
end
end DuplicatePrefix.GeneralBorrowRawRootAcceptedObserved
