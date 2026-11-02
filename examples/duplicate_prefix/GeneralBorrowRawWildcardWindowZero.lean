import duplicate_prefix.GeneralBorrowRawWildcardWindowInitialize
import duplicate_prefix.GeneralBorrowRawWildcardWindowRuntime
import duplicate_prefix.GeneralBorrowFreshRootScopedRootZeroPhysical
namespace DuplicatePrefix.GeneralBorrowRawWildcardWindowZero
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GeneralBorrowRawWildcardWindowInitial
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- A genuine positive wildcard invocation at count zero supplies every current
release and physical return fact internally. No successful operation, final heap,
order certificate or safety property is an input. -/
theorem prepare (s : Initial) :
    ∃ input : GeneralBorrowFreshRootScopedRootZeroPhysical.Input,
      input.options=s.options ∧ input.limits=s.limits ∧ input.remaining=s.remaining ∧ input.span=s.span ∧ input.release.slotId=s.slotId ∧ input.context=s.writeContext ∧
      ActualCall s 0 input.before input.machine := by
  obtain ⟨p⟩ := GeneralBorrowRawWildcardWindowInitialize.initializes s 0
  let raw := RawRootInvocation.root s.before s.place s.race
  let adjusted := GeneralBorrowRawWildcardWindowInitial.adjusted s
  let tag := (GeneralBorrowRawWildcardWindowFunctionState.next s.tracker s.fresh).global.nextPointerTag
  let held := global s
  let frame := caller s 0
  let entered := machine s p.output p.slotAllocation
  have facts := GeneralBorrowRawWildcardWindowRuntime.facts s p.output p.slotAllocation
  obtain ⟨fb,fi,fc,frc,frp,fva,frace,fborrow,floc⟩ := PositiveRootInstalledFrame.metadata raw adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag
  have fsize := PositiveRootInstalledFrame.size raw adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag
  have slots (i : Fin 25) := PositiveRootInstalledFrame.slot_option raw (RawRootInvocation.locals s.before s.place s.race)
    adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag i
  have rootFree : held.global.protectedTags.contains s.slotRoot = false := by
    change ((s.tracker.global.protectedTags.insert s.tracker.global.nextPointerTag .StrongProtector).insert tag .StrongProtector).contains s.slotRoot = false
    have different : s.slotRoot ≠ tag := s.slotDistinct
    rw [ProtectorInsertion.contains_other _ _ _ .StrongProtector different,
      ProtectorInsertion.contains_other _ _ _ .StrongProtector s.slotParentDistinct]
    exact s.slotFree
  have childHeld : held.global.protectedTags.contains tag = true := by
    change (((GeneralBorrowRawWildcardWindowFunctionState.next s.tracker s.fresh).global.protectedTags).insert tag .StrongProtector).contains tag = true
    unfold ProtectedTags.contains
    rw [ProtectedTags.get_insert_same]
    rfl
  let release : GeneralBorrowFreshRootScopedRootReleasePlan.Input entered.memory held.global := {
    id:=s.id,tag:=s.tracker.global.nextPointerTag,buffer:={s.entry with allocation:=s.entry.allocation.setExtra p.output.child.tree},
    present:=p.buffer,anchor:=p.child,selected:=p.child,maximum:=s.tracker.global.nextPointerTag,offset:=offset s,len:=s.len,
    runtime:=p.runtime,positive:=p.positive,node:=p.node,anchorPresent:=p.nodePresent,notExposed:=p.hidden,tagPresent:=p.lookup,
    distinct:=p.distinct,short:=Nat.lt_of_le_of_lt p.growth s.nodeHeadroom,active:=p.activity,slotId:=s.slotId,separate:=s.separate,
    slot:={s.slotEntry with allocation:=p.slotAllocation},slotPresent:=p.slot,slotRoot:=s.slotRoot,slotChild:=tag,
    slotTree:=p.slotProperties.1,slotRootFree:=rootFree,slotChildHeld:=childHeld,slotDistinct:=s.slotDistinct }
  obtain ⟨thread,active,top⟩ := facts.active
  let input : GeneralBorrowFreshRootScopedRootZeroPhysical.Input := {
    options:=s.options,limits:=s.limits,remaining:=s.remaining,span:=s.span,source:=s.source,fuel:=s.validityFuel,
    debugOff:=s.debugOff,validationFuel:=s.validationEq,context:=s.writeContext,validationContext:=s.validationContext,
    accessEq:=s.accessEq,validationWidth:=s.validationWidth,validationRuntimeSize:=s.validationRuntimeSize,sameRuntime:=s.sameRuntime,
    width:=s.width,runtimeWidth:=s.runtimeWidth,runtimeSize:=s.runtimeSize,outerAccessEq:=s.outerAccessEq,
    before:=frame,size:=fsize,location:=floc,slot0:=by simpa [frame,caller] using slots ⟨0,by decide⟩,
    slot3:=by simpa [frame,caller] using slots ⟨3,by decide⟩,slot4:=by simpa [frame,caller] using slots ⟨4,by decide⟩,slot5:=by simpa [frame,caller] using slots ⟨5,by decide⟩,
    slot2:=by simpa [frame,caller] using slots ⟨2,by decide⟩,
    immediate:=PositiveRootInstalledFrame.immediate raw (RawRootInvocation.locals s.before s.place s.race) adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag,
    body:=fb.trans raw.body,identity:=fi.trans raw.identity,callee:=fc.trans raw.callee,noLocalClocks:=frace.trans raw.noClocks,
    continuation:=frc.trans (RawRootInvocation.control s.before s.place s.race).2.2.1,varargs:=by change (PositiveRootInstalledFrame.installed raw adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag).vaList = #[];rw [fva];rfl,
    machine:=entered,tracker:=held,tracked:=p.tracked,defaultMode:=s.mode,noClocks:=facts.race,noBackend:=facts.backend,
    ghost:=facts.ghost,shallow:=facts.shallow,unchecked:=facts.unchecked,noGc:=facts.noGc,fixed:=facts.fixed,
    thread:=thread,active:=active,release:=release,frameTracked:=fborrow,
    slotSize:=p.slotProperties.2.1,slotStorage:=p.slotProperties.2.2.1,
    slotMask:=p.slotProperties.2.2.2.1,slotProvenance:=p.slotProperties.2.2.2.2.1,slotMutable:=p.slotProperties.2.2.2.2.2.2,
    place:=s.place,layout:=s.layout,slotBase:=s.slotBase,slotPointer:=s.slotPointer,aligned:=s.aligned,fits:=s.slotFits,
    cached:=by rw [facts.addresses];exact s.slotCached,
    extras:=by change entered.user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [facts.extras];exact s.extras,
    destination:=by change (PositiveRootInstalledFrame.installed raw adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag).returnPlace.toRuntimePlace = _;rw [frp];rfl }
  exact ⟨input,rfl,rfl,rfl,rfl,rfl,rfl,p.call⟩

theorem invoke (s : Initial) :
    ∃ input : GeneralBorrowFreshRootScopedRootZeroPhysical.Input,
      input.options=s.options ∧ input.limits=s.limits ∧ input.remaining=s.remaining ∧ input.span=s.span ∧ input.release.slotId=s.slotId ∧ input.context=s.writeContext ∧
      ActualCall s 0 input.before input.machine ∧ GeneralBorrowFreshRootScopedRootZeroPhysical.Result input := by
  obtain ⟨input,options,limits,remaining,span,slotId,context,call⟩ := prepare s
  exact ⟨input,options,limits,remaining,span,slotId,context,call,GeneralBorrowFreshRootScopedRootZeroPhysical.complete input⟩
end
end DuplicatePrefix.GeneralBorrowRawWildcardWindowZero
