import duplicate_prefix.GeneralBorrowExposedScopedWritableMutableEntryFromDefault
import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableAcceptedExpression
import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableDefaultNextRaw
import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableDefaultNextGeometry
namespace DuplicatePrefix.GeneralBorrowExposedScopedWindowWritableAcceptedToAsMut
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open GeneralBorrowExposedScopedWindowWritableAcceptedExpression
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

structure Origin (s : Input) (call : GeneralBorrowExposedScopedWindowWritableAsMutCallInput.Input) : Prop where
  options : call.options=s.options
  limits : call.limits=s.limits
  remaining : call.remaining=s.remaining
  span : call.span=s.span
  caller : call.caller=expressionFrame s
  machine : call.machine=expressionMachine s
  id : call.id=s.id
  entry : call.entry=expressionEntry s
  parentTag : call.parentTag=s.tracker.global.nextPointerTag
  tracker : call.tracker=expressionTracker s
  base : call.base=s.base
  offset : call.offset=s.offset
  len : call.len=s.len
  parent : call.data.input.parent=GeneralBorrowFreshMetadataChildDefault.index s.data.input

theorem forms (s : Input) :
    ∃ call : GeneralBorrowExposedScopedWindowWritableAsMutCallInput.Input,
      Origin s call ∧
      ExecutionMachine.step (ActualReferenceContext.config s.options (s.remaining+1) s.span) s.limits ()
        (Storage.withCurrent #[] s.caller s.machine)=(Storage.withCurrent #[] call.caller call.machine,.ok true) := by
  obtain ⟨next,parent,offsetEq,lenEq,clean⟩:=GeneralBorrowExposedScopedWindowWritableDefaultNextRaw.next s.entry.allocation.extra s.tracker.global.protectedTags
    s.parentTag s.tracker.global.nextPointerTag (expressionTracker s).global.nextPointerTag s.offset s.len s.selected s.head s.tail
    s.data s.rangePositive s.futureFresh s.different s.room s.vacantClean
  have geometry:=GeneralBorrowExposedScopedWindowWritableDefaultNextGeometry.frame s.data.input s.tracker.global.protectedTags s.selected s.head s.tail
    s.data.resources .VisitChildrenOfAccessed
  have capacity : (expressionTree s).locations.size=s.entry.allocation.extra.locations.size := by
    simpa only [expressionTree,GeneralBorrowExposedScopedDefaultExpression.child,GeneralBorrowExposedScopedDefaultExpression.read,
      s.data.treeEq,s.data.parentTagEq,s.data.newTagEq,s.data.offsetEq,s.data.lenEq] using geometry.2
  have valid15 : (15 : MIR.LocalId)<(expressionFrame s).locals.size := by
    simpa [expressionFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using s.valid15
  have valid16 : (16 : MIR.LocalId)<(expressionFrame s).locals.size := by
    simpa [expressionFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using s.valid16
  have live15 : (expressionFrame s).locals[15].value=.live (.immediate .uninit) := by
    simpa [expressionFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using s.live15
  have uncached15 : (expressionFrame s).locals[15].layout=none := by
    simpa [expressionFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using s.uncached15
  have source16 : (expressionFrame s).locals[16].value=.live (.immediate (value s)) := by
    simp [expressionFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]
  have cache16 : (expressionFrame s).locals[16].layout=some ActualReferenceMetadata.reference := by
    simp [expressionFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]
  let mutable:=GeneralBorrowExposedScopedWritableMutableEntryFromDefault.convert (expressionTree s) s.tracker.global.protectedTags
    s.tracker.global.nextPointerTag (expressionTracker s).global.nextPointerTag s.offset s.len s.selected s.head s.tail next
  let call : GeneralBorrowExposedScopedWindowWritableAsMutCallInput.Input := {
    options:=s.options,limits:=s.limits,remaining:=s.remaining,span:=s.span,ctx:=s.ctx,debug:=s.debug,
    dynamicFuel:=s.dynamicFuel,dynamic:=s.dynamic,fuel:=s.fuel,validation:=s.validation,cmp:=s.cmp,source:=s.source,budget:=s.budget,dispatch:=s.dispatch,
    caller:=expressionFrame s,machine:=expressionMachine s,id:=s.id,entry:=expressionEntry s,parentTag:=s.tracker.global.nextPointerTag,
    base:=s.base,offset:=s.offset,len:=s.len,positive:=s.positive,nonzero:=s.nonzero,signedFits:=s.signedFits,bounds:=s.bounds,
    capacity:=capacity.trans s.capacity,cachedAddress:=s.cachedAddress,
    present:=StackPopRelease.lookup_commit_same s.machine.memory s.id s.entry (expressionTree s),
    tracker:=expressionTracker s,tracked:=rfl,mode:=s.mode,fresh:=s.nextFresh,selected:=s.selected,head:=s.head,tail:=s.tail,data:=mutable,
    rangePositive:=by
      have positive : s.offset.toNat<(s.offset+s.len).toNat := by simpa only [s.data.offsetEq,s.data.lenEq] using s.rangePositive
      simpa only [mutable,GeneralBorrowExposedScopedWritableMutableEntryFromDefault.convert,
        GeneralBorrowExposedScopedWritableMutableEntryInput.mutableInput,next.offsetEq,next.lenEq] using positive,
    clean:=clean,valid15:=valid15,live15:=live15,uncached15:=uncached15,valid16:=valid16,live16:=source16,cached16:=cache16,
    body:=s.body,identity:=s.identity,callee:=s.callee,location:=rfl,clocks:=s.clocks,ghost:=s.ghost,shallow:=s.shallow,race:=s.race,backend:=s.backend,
    metadata:=s.metadata,notConstructed:=s.notConstructed,thread:=s.thread,active:=s.active,top:=s.top,unchecked:=s.unchecked,noGc:=s.noGc,fixed:=s.fixed }
  exact ⟨call,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,parent⟩,GeneralBorrowExposedScopedWindowWritableAcceptedExpression.step s⟩
end
end DuplicatePrefix.GeneralBorrowExposedScopedWindowWritableAcceptedToAsMut
