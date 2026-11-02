import duplicate_prefix.GeneralBorrowRawWildcardWindowAccepted
import duplicate_prefix.GeneralBorrowFreshRootScopedDefaultFullTrueExit
import duplicate_prefix.DuplicatePrefixArgumentCallResult
import duplicate_prefix.GeneralBorrowRawSliceBytes
namespace DuplicatePrefix.GeneralBorrowRawWildcardWindowAcceptedReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GeneralBorrowRawWildcardWindowInitial
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Accepted branch from ORIGINAL call-time data and count-independent source
bytes. Every intermediate frame, graph, owner, byte-prefix, slot and control fact
is obtained internally from actual initialization/shared/len/mutable/Copy/return. -/
theorem invoke (s : Initial) (n : UInt64) (positiveCount : n ≠ 0) (within : n ≤ s.len/2)
    (preciseOff : s.options.retag.preciseInteriorMut = false)
    (implicitOff : s.options.retag.implicitWrites = false)
    (budget : Nat) (dispatch : s.limits.callDispatch = budget+1)
    (nodeMargin : s.entry.allocation.extra.nodes.size+5 < 65536)
    (tagMargin : s.tracker.global.nextPointerTag.value.toNat+5 < 18446744073709551615)
    (bytes : GeneralBorrowRawSliceBytes.Data s.entry.allocation (offset s) s.len)
    (bufferExtras : s.before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == s.id) = some (s.id,⟨none,#[]⟩))
    (statementFuel : s.limits.validation = s.validityFuel+1) :
    DuplicatePrefixArgumentCallResult.Result s.options s.limits s.remaining s.span s.before
      (.pointer (Pointer.new .wildcard (Size.ofBytes s.address))) s.len n s.place := by
  obtain ⟨outcome⟩ := GeneralBorrowRawWildcardWindowAccepted.executes s n positiveCount within preciseOff implicitOff budget dispatch (by omega) (by omega)
  let frame := outcome.frame
  let initial := machine s outcome.entry.output outcome.entry.slotAllocation
  have addressEq : s.base+offset s = s.address := by rw [UInt64.add_comm];exact UInt64.sub_add_cancel _ _
  let post := outcome.post
  let tag := (GeneralBorrowRawWildcardWindowFunctionState.next s.tracker s.fresh).global.nextPointerTag
  let rawFrame := RawRootInvocation.root s.before s.place s.race
  obtain ⟨fb,fi,fc,frc,frp,fva,frace,fborrow,floc⟩ := PositiveRootInstalledFrame.metadata rawFrame (adjusted s) n {} s.id s.tracker.global.nextPointerTag s.slotId tag
  have rootFree : (global s).global.protectedTags.contains s.slotRoot = false := by
    change ((s.tracker.global.protectedTags.insert s.tracker.global.nextPointerTag .StrongProtector).insert tag .StrongProtector).contains s.slotRoot = false
    have different : s.slotRoot ≠ tag := s.slotDistinct
    rw [ProtectorInsertion.contains_other _ _ _ .StrongProtector different,
      ProtectorInsertion.contains_other _ _ _ .StrongProtector s.slotParentDistinct]
    exact s.slotFree
  have childHeld : (global s).global.protectedTags.contains tag = true := by
    change (((GeneralBorrowRawWildcardWindowFunctionState.next s.tracker s.fresh).global.protectedTags).insert tag .StrongProtector).contains tag = true
    unfold ProtectedTags.contains
    rw [ProtectedTags.get_insert_same]
    rfl
  obtain ⟨node,present,nodeTag,parent,hidden,currentLookup⟩ := outcome.graph.oldNodes outcome.entry.child outcome.entry.node outcome.entry.nodePresent
  have growth : outcome.tree.nodes.size ≤ s.entry.allocation.extra.nodes.size+3 := by
    have first := outcome.entry.growth
    have last := outcome.graph.growth
    omega
  have counter : outcome.tracker.global.nextPointerTag.value.toNat = s.tracker.global.nextPointerTag.value.toNat+4 := by
    have first := GenericFunctionEntryNumerics.successor_value s.tracker.global.nextPointerTag s.fresh
    have second := GenericFunctionEntryNumerics.successor_value (GeneralBorrowRawWildcardWindowFunctionState.next s.tracker s.fresh).global.nextPointerTag s.slotFresh
    have last := outcome.graph.tagCounter
    change (GeneralBorrowRawWildcardWindowFunctionState.next s.tracker s.fresh).global.nextPointerTag.value.toNat = s.tracker.global.nextPointerTag.value.toNat+1 at first
    change (global s).global.nextPointerTag.value.toNat = (GeneralBorrowRawWildcardWindowFunctionState.next s.tracker s.fresh).global.nextPointerTag.value.toNat+1 at second
    omega
  have fresh : outcome.tracker.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change outcome.tracker.global.nextPointerTag.value.toNat < 18446744073709551615
    omega
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {s.entry with allocation:=s.entry.allocation.setExtra outcome.tree}
  let raw : GeneralBorrowFreshRootScopedDefault.Input outcome.tree outcome.tracker.global := {
    parentTag:=s.tracker.global.nextPointerTag,parent:=outcome.entry.child,selected:=outcome.entry.child,maximum:=s.tracker.global.nextPointerTag,
    offset:=offset s,len:=s.len,tagged:=by rw [←outcome.entry.nodeTag];exact currentLookup,
    positive:=outcome.owner,distinct:=outcome.graph.distinct,short:=outcome.graph.short,
    nodeRoom:=by have h:=outcome.graph.short;omega,tagRoom:=fresh}
  have bufferPresent : post.memory.live.find? (fun row => row.1 == s.id) = some (s.id,entry) := by
    rw [outcome.memory]
    exact StackPopRelease.lookup_commit_same initial.memory s.id _ outcome.tree
  have slotPresent : post.memory.live.find? (fun row => row.1 == s.slotId) = some (s.slotId,{s.slotEntry with allocation:=outcome.entry.slotAllocation}) := by
    rw [outcome.memory]
    exact StackPopRelease.lookup_commit_other initial.memory s.id s.slotId _ _ outcome.tree s.separate outcome.entry.slot
  obtain ⟨thread,active,top⟩ := outcome.flags.active
  have valid (i : Fin 25) : i.val < frame.locals.size := by rw [outcome.size];exact i.isLt
  have cell (i : Fin 25) (row : LocalState Provenance LocalLayout) (present : frame.locals[i.val]? = some row) : frame.locals[i.val]'(valid i) = row :=
    Option.some.inj ((Array.getElem?_eq_getElem (valid i)).symm.trans present)
  have sourceCell := cell ⟨1,by decide⟩ _ outcome.source
  have destCell := cell ⟨15,by decide⟩ _ outcome.temp15
  have tempCell := cell ⟨16,by decide⟩ _ outcome.temp16
  let ret : GeneralBorrowFreshRootScopedTrueReturnData.Data s.options s.remaining s.span frame post outcome.tracker s.id entry s.tracker.global.nextPointerTag raw.parent := {
    context:=s.writeContext,
    validationContext:=s.validationContext,accessEq:=s.accessEq,
    validationWidth:=s.validationWidth,
    validationRuntimeSize:=s.validationRuntimeSize,
    sameRuntime:=s.sameRuntime,
    width:=s.width,
    runtimeWidth:=s.runtimeWidth,
    runtimeSize:=s.runtimeSize,
    outerAccessEq:=s.outerAccessEq,
    sourceNode:=node,
    sourcePresent:=present,
    sourceTag:=nodeTag.trans outcome.entry.nodeTag,
    sourceHidden:=hidden.trans outcome.entry.hidden,
    continuation:=outcome.metadata.continuation.trans (frc.trans (RawRootInvocation.control s.before s.place s.race).2.2.1),
    varargs:=by rw [outcome.metadata.varargs];change (PositiveRootInstalledFrame.installed rawFrame (adjusted s) n {} s.id s.tracker.global.nextPointerTag s.slotId tag).vaList = #[];rw [fva];rfl,
    slotId:=s.slotId,
    separate:=s.separate,
    slot:={s.slotEntry with allocation:=outcome.entry.slotAllocation},
    slotBefore:=slotPresent,
    slotRoot:=s.slotRoot,
    slotChild:=tag,
    slotTree:=outcome.entry.slotProperties.1,
    slotRootFree:=by rw [outcome.graph.protections];exact rootFree,
    slotChildHeld:=by rw [outcome.graph.protections];exact childHeld,
    slotDistinct:=s.slotDistinct,
    frameTracked:=by rw [outcome.metadata.extra];exact fborrow,
    slotSize:=outcome.entry.slotProperties.2.1,
    slotStorage:=outcome.entry.slotProperties.2.2.1,
    slotMask:=outcome.entry.slotProperties.2.2.2.1,
    slotProvenance:=outcome.entry.slotProperties.2.2.2.2.1,
    slotMutable:=outcome.entry.slotProperties.2.2.2.2.2.2,
    place:=s.place,
    layout:=s.layout,
    slotBase:=s.slotBase,
    slotPointer:=s.slotPointer,
    aligned:=s.aligned,
    fits:=s.slotFits,
    cached:=by rw [outcome.flags.addresses];exact s.slotCached,
    extras:=by change post.user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [outcome.flags.extras];exact s.extras,
    destination:=by rw [outcome.metadata.returnPlace.trans frp];rfl }
  have byteFacts := (bytes.set_extra outcome.tree).for_count n (UInt64.pos_iff_ne_zero.mpr positiveCount) within
  obtain ⟨physical,value,slotId,result,updated,suffixTrace,terminal,safe⟩ :=
    GeneralBorrowFreshRootScopedDefaultFullTrueExit.invoke s.options s.limits s.remaining s.span s.ctx s.debugOff s.cmp s.dynamicFuel s.validityFuel
      s.fuelEq s.validationEq s.id entry s.base (offset s) s.len s.tracker.global.nextPointerTag s.positive (by rw [addressEq];exact s.nonzero) s.signedFits s.bounds
      frame post outcome.tracker outcome.tracked outcome.mode fresh outcome.formed raw rfl rfl rfl
      (outcome.graph.capacity.trans (outcome.entry.capacity.trans s.capacity)) (valid ⟨15,by decide⟩)
      (congrArg LocalState.value destCell) (congrArg LocalState.layout destCell) (by rw [outcome.metadata.extra];change (PositiveRootInstalledFrame.installed rawFrame (adjusted s) n {} s.id s.tracker.global.nextPointerTag s.slotId tag).extra.dataRace = none;rw [frace];exact rawFrame.noClocks) outcome.flags.ghost outcome.flags.shallow
      (by rw [outcome.flags.addresses];exact s.cachedAddress) bufferPresent outcome.flags.race
      (by change post.user.payload.payload.user.types.metadata = _;rw [outcome.flags.types];exact s.metadata)
      (by change post.user.payload.payload.user.types.entries.any _ = _;rw [outcome.flags.types];exact s.notConstructed)
      thread active (by change outcome.tree.nodes.size+2 < 65536;omega) (by omega) preciseOff implicitOff s.source budget dispatch outcome.flags.backend outcome.flags.unchecked outcome.flags.noGc outcome.flags.fixed top
      outcome.size (outcome.metadata.body.trans (fb.trans rawFrame.body)) (outcome.metadata.identity.trans (fi.trans rawFrame.identity)) (outcome.metadata.callee.trans (fc.trans rawFrame.callee)) (by rw [outcome.track];rfl) (by rw [outcome.metadata.extra];change (255:UInt8)>0;decide) outcome.immediate outcome.location
      (valid ⟨16,by decide⟩) (congrArg LocalState.value tempCell) (congrArg LocalState.layout tempCell) (valid ⟨1,by decide⟩)
      (by simpa only [adjusted,ActualReferenceContext.config,CanonicalConfigFacts.actual_access_runtime,addressEq] using congrArg LocalState.value sourceCell)
      (congrArg LocalState.layout sourceCell) n byteFacts.positive within outcome.count outcome.flag outcome.high
      outcome.activity outcome.zero statementFuel byteFacts.storage byteFacts.maskValid byteFacts.maskLen byteFacts.initialized byteFacts.provenance byteFacts.storageFits byteFacts.mutable
      (by rw [outcome.flags.extras];exact bufferExtras) (byteFacts.bounded s.options s.remaining s.span) ret
  have fullTrace := SuccessfulTrace.append outcome.trace suffixTrace
  let terminalState := CanonicalCopy.replaceAllocation (GeneralBorrowFreshRootScopedRootBoolReturn.popped physical) physical.release.slotId physical.release.slot.kind updated
  have entryCall : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] (caller s n) initial) := by simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent]
  have past : CallSafety.pastCallBoundary 1 terminalState := by change (0:Nat)<1;decide
  have wholeSafe := SuccessfulTrace.no_ub ⟨config s.options (s.remaining+1) s.span,s.limits,fun _ _ => True⟩ 1 _ terminalState entryCall fullTrace past
  apply (DuplicatePrefixArgumentCallResult.pointer_iff _ _ _ _ _ _ _ _ _).mpr
  exact ⟨Storage.withCurrent #[] (caller s n) initial,terminalState,outcome.entry.call,fullTrace,terminal,rfl,
    SuccessfulTrace.no_errors ⟨config s.options (s.remaining+1) s.span,s.limits,fun _ _ => True⟩ 1 _ terminalState entryCall fullTrace past,
    wholeSafe,SuccessfulTraceTerminal.prefix_step_success fullTrace terminal⟩
end
end DuplicatePrefix.GeneralBorrowRawWildcardWindowAcceptedReturn
