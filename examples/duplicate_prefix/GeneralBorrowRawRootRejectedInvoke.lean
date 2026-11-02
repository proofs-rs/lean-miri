import duplicate_prefix.GeneralBorrowRawRootRejectedLedger
import duplicate_prefix.GeneralBorrowRawRootInitialSlot
import duplicate_prefix.GeneralBorrowRawRootInitialNode
import duplicate_prefix.GeneralBorrowRawRootCurrentBoolReturn
namespace DuplicatePrefix.GeneralBorrowRawRootRejectedInvoke
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
abbrev Initial := GeneralBorrowRawRootZeroEntry.Initial

structure Prepared (s : Initial) (n : UInt64) where
  entry : CompilerFrameContext.ActualFrame
  initial : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  call : GeneralBorrowRawRootPositivePrefix.ActualCall s n entry initial
  current : GeneralBorrowRawRootCurrentBoolReturn.Input
  options : current.options = s.options
  limits : current.limits = s.limits
  remaining : current.remaining = s.remaining
  span : current.span = s.span
  value : current.value = false
  slotId : current.slotId = s.slotId
  trace : SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits
    (Storage.withCurrent #[] entry initial) (Storage.withCurrent #[] current.before current.machine)

/-- Form the physical false-return packet from the ORIGINAL caller state.
The current root node, owner, activity, protection map, frame and slot lookup
are all derived from actual execution and the preserved initial slot ledger. -/
theorem prepare (s : Initial) (n : UInt64) (positiveCount : n ≠ 0) (rejected : n > s.len/2)
    (preciseOff : s.options.retag.preciseInteriorMut = false)
    (implicitOff : s.options.retag.implicitWrites = false)
    (budget : Nat) (dispatch : s.limits.callDispatch = budget+1)
    (nodeMargin : s.entry.allocation.extra.nodes.size+3 < 65536)
    (tagMargin : s.tracker.global.nextPointerTag.value.toNat+3 < 18446744073709551615) :
    Nonempty (Prepared s n) := by
  obtain ⟨entryFrame,frame,initial,machine,call,entryEq,trace,frameFacts,⟨heap⟩⟩ :=
    GeneralBorrowRawRootRejectedLedger.executes s n positiveCount rejected preciseOff implicitOff budget dispatch nodeMargin tagMargin
  obtain ⟨slot⟩ := GeneralBorrowRawRootInitialSlot.of_call s n entryFrame initial call
  obtain ⟨anchor,oldNode,lookup,oldPresent,oldTag,oldHidden⟩ := GeneralBorrowRawRootInitialNode.exists_node s
  have anchorEq : anchor = heap.observer := Option.some.inj (lookup.symm.trans heap.originalTagged)
  subst anchor
  obtain ⟨node,present,tag,parent,hidden,currentLookup⟩ := heap.graph.oldNodes heap.observer oldNode oldPresent
  obtain ⟨owner⟩ := heap.original
  obtain ⟨thread,active,top⟩ := heap.runtime.active
  let raw := RawRootInvocation.root s.before s.place s.race
  let adjusted := GeneralBorrowRawRootPrefixFrame.sourceValue s
  have rootMeta := PositiveRootInstalledFrame.metadata raw adjusted n {} s.id s.tracker.global.nextPointerTag
    s.slotId (GeneralBorrowRawRootInitialSlot.slotTag s)
  have rootClocks : (GeneralBorrowRawRootInitialize.caller s n).extra.dataRace = none :=
    rootMeta.2.2.2.2.2.2.1.trans raw.noClocks
  have rootContinuation : (GeneralBorrowRawRootInitialize.caller s n).returnContinuation = .stop true :=
    rootMeta.2.2.2.1.trans (RawRootInvocation.control s.before s.place s.race).2.2.1
  have rootVarargs : (GeneralBorrowRawRootInitialize.caller s n).vaList = #[] := by
    change (PositiveRootInstalledFrame.installed raw adjusted n {} s.id s.tracker.global.nextPointerTag s.slotId
      (GeneralBorrowRawRootInitialSlot.slotTag s)).vaList = #[]
    rw [rootMeta.2.2.2.2.2.1]
    rfl
  have rootDestination : (GeneralBorrowRawRootInitialize.caller s n).returnPlace.toRuntimePlace = ⟨.memory s.place.mplace,s.place.layout⟩ := by
    change (PositiveRootInstalledFrame.installed raw adjusted n {} s.id s.tracker.global.nextPointerTag s.slotId
      (GeneralBorrowRawRootInitialSlot.slotTag s)).returnPlace.toRuntimePlace = _
    rw [rootMeta.2.2.2.2.1]
    rfl
  have slotRootFree : heap.tracker.global.protectedTags.contains s.slotRoot = false := by
    rw [heap.graph.protections]
    exact slot.rootFree
  have slotChildHeld : heap.tracker.global.protectedTags.contains (GeneralBorrowRawRootInitialSlot.slotTag s) = true := by
    rw [heap.graph.protections]
    exact slot.childHeld
  let input : GeneralBorrowRawRootCurrentBoolReturn.Input := {
    options:=s.options,limits:=s.limits,remaining:=s.remaining,span:=s.span,fuel:=s.validityFuel,
    debugOff:=s.debugOff,validationFuel:=s.validationEq,context:=s.writeContext,validationContext:=s.validationContext,
    accessEq:=s.accessEq,validationWidth:=s.validationWidth,validationRuntimeSize:=s.validationRuntimeSize,sameRuntime:=s.sameRuntime,
    width:=s.width,runtimeWidth:=s.runtimeWidth,runtimeSize:=s.runtimeSize,outerAccessEq:=s.outerAccessEq,
    before:=frame,size:=frameFacts.size,location:=frameFacts.location,value:=false,slot0:=frameFacts.value,
    immediate:=frameFacts.immediate,body:=frameFacts.body,identity:=frameFacts.identity,callee:=frameFacts.callee,
    noLocalClocks:=by rw [frameFacts.extra,entryEq];exact rootClocks,
    continuation:=by rw [frameFacts.continuation,entryEq];exact rootContinuation,
    varargs:=by rw [frameFacts.varargs,entryEq];exact rootVarargs,
    machine:=machine,tracker:=heap.tracker,tracked:=heap.tracked,noClocks:=heap.runtime.race,noBackend:=heap.runtime.backend,
    ghost:=heap.runtime.ghost,shallow:=heap.runtime.shallow,unchecked:=heap.runtime.unchecked,noGc:=heap.runtime.noGc,
    fixed:=heap.runtime.fixed,thread:=thread,active:=active,baseline:=initial.memory,id:=s.id,entry:=s.entry,tree:=heap.tree,
    memoryEq:=heap.memory,tag:=s.tracker.global.nextPointerTag,anchor:=heap.observer,selected:=s.raw.selected,
    maximum:=s.raw.maximum,offset:=s.offset,len:=s.len,runtime:=heap.formed,positive:=owner,node:=node,present:=present,
    sameTag:=tag.trans oldTag,hidden:=hidden.trans oldHidden,distinct:=heap.graph.distinct,order:=heap.graph.order,short:=heap.graph.short,
    activity:=heap.originalActivity,slotId:=s.slotId,separate:=s.separate,slot:=slot.slot,slotBefore:=slot.present,
    slotRoot:=s.slotRoot,slotChild:=GeneralBorrowRawRootInitialSlot.slotTag s,slotTree:=slot.tree,
    slotRootFree:=slotRootFree,slotChildHeld:=slotChildHeld,slotDistinct:=slot.distinct,
    frameTracked:=by rw [frameFacts.extra,entryEq];exact GeneralBorrowRawRootInitialSlot.frame s n,
    slotSize:=slot.size,slotStorage:=slot.storage,slotMask:=slot.mask,slotProvenance:=slot.provenance,slotMutable:=slot.mutable,
    place:=s.place,layout:=s.layout,slotBase:=s.slotBase,slotPointer:=s.slotPointer,aligned:=s.aligned,fits:=s.slotFits,
    cached:=by rw [heap.runtime.addresses];exact s.slotCached,
    extras:=by change machine.user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [heap.runtime.extras];exact s.extras,
    destination:=by rw [frameFacts.returnPlace,entryEq];exact rootDestination }
  exact ⟨⟨entryFrame, initial, call, input, rfl, rfl, rfl, rfl, rfl, rfl, trace⟩⟩
end
end DuplicatePrefix.GeneralBorrowRawRootRejectedInvoke
