import duplicate_prefix.GeneralBorrowRawWildcardWindowRejected
import duplicate_prefix.GeneralBorrowFreshRootScopedRootCurrentBoolReturn
import duplicate_prefix.DuplicatePrefixArgumentCallResult
namespace DuplicatePrefix.GeneralBorrowRawWildcardWindowRejectedReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GeneralBorrowRawWildcardWindowInitial
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

theorem invoke (s : Initial) (n : UInt64) (nonzeroCount : n ≠ 0) (rejected : n > s.len/2)
    (preciseOff : s.options.retag.preciseInteriorMut = false)
    (implicitOff : s.options.retag.implicitWrites = false)
    (budget : Nat) (dispatch : s.limits.callDispatch = budget+1)
    (nodeMargin : s.entry.allocation.extra.nodes.size+3 < 65536)
    (tagMargin : s.tracker.global.nextPointerTag.value.toNat+3 < 18446744073709551615) :
    DuplicatePrefixArgumentCallResult.Result s.options s.limits s.remaining s.span s.before
      (.pointer (Pointer.new .wildcard (Size.ofBytes s.address))) s.len n s.place := by
  obtain ⟨p⟩ := GeneralBorrowRawWildcardWindowRejected.executes s n nonzeroCount rejected preciseOff implicitOff budget dispatch nodeMargin tagMargin
  let tag := (GeneralBorrowRawWildcardWindowFunctionState.next s.tracker s.fresh).global.nextPointerTag
  let raw := RawRootInvocation.root s.before s.place s.race
  obtain ⟨fb,fi,fc,frc,frp,fva,frace,fborrow,floc⟩ := PositiveRootInstalledFrame.metadata raw (adjusted s) n {} s.id s.tracker.global.nextPointerTag s.slotId tag
  obtain ⟨node,present,sameTag,parent,hidden,lookup⟩ := p.graph.oldNodes p.entry.child p.entry.node p.entry.nodePresent
  obtain ⟨thread,active,top⟩ := p.flags.active
  have rootFree : p.tracker.global.protectedTags.contains s.slotRoot = false := by
    rw [p.graph.protections]
    change ((s.tracker.global.protectedTags.insert s.tracker.global.nextPointerTag .StrongProtector).insert tag .StrongProtector).contains s.slotRoot = false
    have different : s.slotRoot ≠ tag := s.slotDistinct
    rw [ProtectorInsertion.contains_other _ _ _ .StrongProtector different,
      ProtectorInsertion.contains_other _ _ _ .StrongProtector s.slotParentDistinct]
    exact s.slotFree
  have childHeld : p.tracker.global.protectedTags.contains tag = true := by
    rw [p.graph.protections]
    change (((GeneralBorrowRawWildcardWindowFunctionState.next s.tracker s.fresh).global.protectedTags).insert tag .StrongProtector).contains tag = true
    unfold ProtectedTags.contains
    rw [ProtectedTags.get_insert_same]
    rfl
  let input : GeneralBorrowFreshRootScopedRootCurrentBoolReturn.Input := {
    options:=s.options,limits:=s.limits,remaining:=s.remaining,span:=s.span,fuel:=s.validityFuel,
    debugOff:=s.debugOff,validationFuel:=s.validationEq,context:=s.writeContext,validationContext:=s.validationContext,
    accessEq:=s.accessEq,validationWidth:=s.validationWidth,validationRuntimeSize:=s.validationRuntimeSize,sameRuntime:=s.sameRuntime,
    width:=s.width,runtimeWidth:=s.runtimeWidth,runtimeSize:=s.runtimeSize,outerAccessEq:=s.outerAccessEq,
    before:=p.frame,size:=p.size,location:=p.location,value:=false,slot0:=p.value,immediate:=p.immediate,
    body:=p.metadata.body.trans (fb.trans raw.body),identity:=p.metadata.identity.trans (fi.trans raw.identity),callee:=p.metadata.callee.trans (fc.trans raw.callee),
    noLocalClocks:=by rw [p.metadata.extra];exact frace.trans raw.noClocks,
    continuation:=p.metadata.continuation.trans (frc.trans (RawRootInvocation.control s.before s.place s.race).2.2.1),
    varargs:=by rw [p.metadata.varargs];change (PositiveRootInstalledFrame.installed raw (adjusted s) n {} s.id s.tracker.global.nextPointerTag s.slotId tag).vaList = #[];rw [fva];rfl,
    machine:=p.post,tracker:=p.tracker,tracked:=p.tracked,noClocks:=p.flags.race,noBackend:=p.flags.backend,
    ghost:=p.flags.ghost,shallow:=p.flags.shallow,unchecked:=p.flags.unchecked,noGc:=p.flags.noGc,fixed:=p.flags.fixed,
    thread:=thread,active:=active,baseline:=(machine s p.entry.output p.entry.slotAllocation).memory,id:=s.id,
    entry:={s.entry with allocation:=s.entry.allocation.setExtra p.entry.output.child.tree},tree:=p.tree,memoryEq:=p.memory,
    tag:=s.tracker.global.nextPointerTag,anchor:=p.entry.child,selected:=p.entry.child,maximum:=s.tracker.global.nextPointerTag,
    offset:=offset s,len:=s.len,runtime:=p.formed,positive:=p.owner,node:=node,present:=present,sameTag:=sameTag.trans p.entry.nodeTag,
    hidden:=hidden.trans p.entry.hidden,distinct:=p.graph.distinct,short:=p.graph.short,activity:=p.activity,
    slotId:=s.slotId,separate:=s.separate,slot:={s.slotEntry with allocation:=p.entry.slotAllocation},slotBefore:=p.entry.slot,
    slotRoot:=s.slotRoot,slotChild:=tag,slotTree:=p.entry.slotProperties.1,slotRootFree:=rootFree,slotChildHeld:=childHeld,slotDistinct:=s.slotDistinct,
    frameTracked:=by rw [p.metadata.extra];exact fborrow,
    slotSize:=p.entry.slotProperties.2.1,slotStorage:=p.entry.slotProperties.2.2.1,
    slotMask:=p.entry.slotProperties.2.2.2.1,slotProvenance:=p.entry.slotProperties.2.2.2.2.1,slotMutable:=p.entry.slotProperties.2.2.2.2.2.2,
    place:=s.place,layout:=s.layout,slotBase:=s.slotBase,slotPointer:=s.slotPointer,aligned:=s.aligned,fits:=s.slotFits,
    cached:=by rw [p.flags.addresses];exact s.slotCached,
    extras:=by change p.post.user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [p.flags.extras];exact s.extras,
    destination:=by rw [p.metadata.returnPlace];change (PositiveRootInstalledFrame.installed raw (adjusted s) n {} s.id s.tracker.global.nextPointerTag s.slotId tag).returnPlace.toRuntimePlace = _;rw [frp];rfl }
  obtain ⟨result⟩ := GeneralBorrowFreshRootScopedRootCurrentBoolReturn.complete input
  obtain ⟨updated,exitTrace,terminal,_,rest⟩ := result.returned
  let final := CanonicalCopy.replaceAllocation (GeneralBorrowFreshRootScopedRootBoolReturn.popped result.physical)
    result.physical.release.slotId result.physical.release.slot.kind updated
  have exit : SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits
      (Storage.withCurrent #[] p.frame p.post) final := by
    simpa only [GeneralBorrowFreshRootScopedRootBoolReturn.caller,result.options,result.remaining,result.span,result.limits,result.before,result.machine] using exitTrace
  have trace := SuccessfulTrace.append p.trace exit
  have entry : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] (caller s n) (machine s p.entry.output p.entry.slotAllocation)) := ⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 final := by change 0<1;decide
  apply (DuplicatePrefixArgumentCallResult.pointer_iff _ _ _ _ _ _ _ _ _).mpr
  refine ⟨_,final,p.entry.call,trace,?_,rfl,SuccessfulTrace.no_errors _ 1 _ _ entry trace past,
    SuccessfulTrace.no_ub _ 1 _ _ entry trace past,SuccessfulTraceTerminal.prefix_step_success trace ?_⟩
  all_goals simpa only [result.options,result.remaining,result.span,result.limits] using terminal
end
end DuplicatePrefix.GeneralBorrowRawWildcardWindowRejectedReturn
