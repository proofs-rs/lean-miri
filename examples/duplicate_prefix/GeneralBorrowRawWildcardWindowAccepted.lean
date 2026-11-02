import duplicate_prefix.GeneralBorrowRawWildcardWindowPrefix
import duplicate_prefix.GeneralBorrowRawWildcardWindowPrefixFacts
import duplicate_prefix.GeneralBorrowFreshRootScopedSharedToAcceptedPhysicalLedger
import duplicate_prefix.GeneralBorrowFreshRootScopedLenNextDefault
namespace DuplicatePrefix.GeneralBorrowRawWildcardWindowAccepted
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GeneralBorrowRawWildcardWindowInitial
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
structure Outcome (s : Initial) (n : UInt64) where
  entry : GeneralBorrowRawWildcardWindowInitialize.Packet s n
  frame : CompilerFrameContext.ActualFrame
  post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  trace : SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits
    (Storage.withCurrent #[] (caller s n) (machine s entry.output entry.slotAllocation)) (Storage.withCurrent #[] frame post)
  tree : BorrowTree
  tracker : MachineHooks.BorrowState
  memory : post.memory = RetagEntry.updatedMemory (machine s entry.output entry.slotAllocation).memory s.id
    {s.entry with allocation:=s.entry.allocation.setExtra entry.output.child.tree} tree
  tracked : post.borrowTracker = some tracker
  mode : tracker.retagMode = .Default
  formed : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global
  owner : GeneralBorrowFreshRootScopedRow.Positive tree tracker.global.protectedTags entry.child entry.child s.tracker.global.nextPointerTag (offset s) s.len
  activity : GeneralBorrowFreshActiveWithin.ActiveWithin tree entry.child .Write (offset s) (offset s+s.len)
  graph : GeneralBorrowFreshRootScopedSharedToLenLedger.Graph entry.output.child.tree tree entry.child (global s) tracker
  flags : GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.before post
  metadata : GeneralBorrowFreshRootScopedPhaseFrame.Frame (caller s n) frame
  track : frame.trackCallerArg = (caller s n).trackCallerArg
  location : frame.location = .mir ⟨6,7⟩
  size : frame.locals.size = 25
  source : frame.locals[1]? = some ⟨.live (.immediate (adjusted s)),some ActualReferenceMetadata.reference⟩
  count : frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩
  flag : frame.locals[13]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩
  temp15 : frame.locals[15]? = some ⟨.live (.immediate .uninit),none⟩
  temp16 : frame.locals[16]? = some ⟨.live (.immediate .uninit),none⟩
  high : ∀ index,17 ≤ index → index ≤ 24 → frame.locals[index]? = some ⟨.dead,none⟩
  immediate : CopyHelperCleanup.AllImmediate frame
  zero : frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩

private theorem cell (frame : CompilerFrameContext.ActualFrame) (i : Nat) (valid : i < frame.locals.size)
    (row : LocalState Provenance LocalLayout) (present : frame.locals[i]? = some row) : frame.locals[i] = row :=
  Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans present)

theorem executes (s : Initial) (n : UInt64) (nonzeroCount : n ≠ 0) (within : n ≤ s.len/2)
    (preciseOff : s.options.retag.preciseInteriorMut = false)
    (implicitOff : s.options.retag.implicitWrites = false)
    (budget : Nat) (dispatch : s.limits.callDispatch = budget+1)
    (nodeMargin : s.entry.allocation.extra.nodes.size+3 < 65536)
    (tagMargin : s.tracker.global.nextPointerTag.value.toNat+3 < 18446744073709551615) :
    Nonempty (Outcome s n) := by
  obtain ⟨packet⟩ := GeneralBorrowRawWildcardWindowPrefix.executes s n (UInt64.pos_iff_ne_zero.mpr nonzeroCount)
  let initial := machine s packet.entry.output packet.entry.slotAllocation
  let current := RootZeroCompleteState.tick s.options s.remaining s.span initial
  let buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind := {s.entry with allocation:=s.entry.allocation.setExtra packet.entry.output.child.tree}
  have facts := GeneralBorrowRawWildcardWindowPrefixFacts.of_shape s n packet.result packet.shape
  have valid (i : Fin 25) : i.val < packet.result.locals.size := by rw [packet.ready.size];exact i.isLt
  have sourceCell := cell packet.result 1 (valid ⟨1,by decide⟩) _ packet.ready.source
  have destCell := cell packet.result 12 (valid ⟨12,by decide⟩) _ packet.ready.exprSlot
  have lenCell := cell packet.result 11 (valid ⟨11,by decide⟩) _ packet.ready.lenSlot
  have zeroCell := cell packet.result 0 (valid ⟨0,by decide⟩) _ facts.zero
  have sevenCell := cell packet.result 7 (valid ⟨7,by decide⟩) _ packet.ready.slot7
  have eightCell := cell packet.result 8 (valid ⟨8,by decide⟩) _ packet.ready.slot8
  have nineCell := cell packet.result 9 (valid ⟨9,by decide⟩) _ packet.ready.slot9
  have tenCell := cell packet.result 10 (valid ⟨10,by decide⟩) _ packet.ready.slot10
  have thirteenCell := cell packet.result 13 (valid ⟨13,by decide⟩) _ facts.thirteen
  have fifteenCell := cell packet.result 15 (valid ⟨15,by decide⟩) _ facts.fifteen
  have sixteenCell := cell packet.result 16 (valid ⟨16,by decide⟩) _ facts.sixteen
  have addressEq : s.base+offset s = s.address := by rw [UInt64.add_comm];exact UInt64.sub_add_cancel _ _
  have sourceLive : (packet.result.locals[1]'(valid ⟨1,by decide⟩)).value = .live (.immediate (RetagReferencePlace.sliceValue
      (config s.options (s.remaining+1) s.span).access.runtime.base
      (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+offset s))) s.len ActualReferenceMetadata.reference).imm) := by
    simpa only [adjusted,addressEq,CanonicalConfigFacts.actual_access_runtime] using congrArg LocalState.value sourceCell
  have metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] packet.result current)).metadata = PreparedReflection.actual.runtime := by
    change current.user.payload.payload.user.types.metadata = _
    rw [packet.flags.types];exact s.metadata
  have uncached : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] packet.result current)).entries.any (·.value.ty == 4) = false := by
    change current.user.payload.payload.user.types.entries.any (·.value.ty == 4) = _
    rw [packet.flags.types];exact s.notConstructed
  have fresh : (global s).global.nextPointerTag.value < 18446744073709551615 := packet.input.tagRoom
  have counter : (global s).global.nextPointerTag.value.toNat = s.tracker.global.nextPointerTag.value.toNat+2 := by
    have first := GenericFunctionEntryNumerics.successor_value s.tracker.global.nextPointerTag s.fresh
    have second := GenericFunctionEntryNumerics.successor_value (GeneralBorrowRawWildcardWindowFunctionState.next s.tracker s.fresh).global.nextPointerTag s.slotFresh
    change (GeneralBorrowRawWildcardWindowFunctionState.next s.tracker s.fresh).global.nextPointerTag.value.toNat = s.tracker.global.nextPointerTag.value.toNat+1 at first
    change (global s).global.nextPointerTag.value.toNat = (GeneralBorrowRawWildcardWindowFunctionState.next s.tracker s.fresh).global.nextPointerTag.value.toNat+1 at second
    omega
  obtain ⟨thread,active,top⟩ := packet.flags.active
  have both : GeneralBorrowFreshRootScopedRow.Positive packet.entry.output.child.tree (global s).global.protectedTags
      packet.input.parent packet.input.selected packet.input.maximum (offset s) s.len := by
    rw [packet.parent,packet.selected,packet.maximum];exact packet.entry.positive
  have activity : GeneralBorrowFreshActiveWithin.ActiveWithin packet.entry.output.child.tree packet.input.parent .Write (offset s) (offset s+s.len) := by
    rw [packet.parent];exact packet.entry.activity
  obtain ⟨result,post,tree,held,child,trace,location,size,source,count,flag,temp15,temp16,high,immediate,memoryAfter,trackedAfter,modeAfter,
    runtimeAfter,_,⟨owner⟩,activityAfter,zero,graph,track,frame,runtime⟩ :=
    GeneralBorrowFreshRootScopedSharedToAcceptedPhysicalLedger.complete s.options s.limits s.remaining s.span preciseOff implicitOff s.debugOff s.cmp
      s.dynamicFuel s.validityFuel s.fuelEq s.validationEq s.base (offset s) s.len s.id buffer s.positive (by rw [addressEq];exact s.nonzero) s.signedFits
      #[] packet.result current packet.ready.body packet.ready.identity packet.ready.callee packet.ready.location (global s) packet.tracked s.mode fresh
      s.tracker.global.nextPointerTag packet.entry.runtime packet.input packet.parentTag packet.inputOffset packet.inputLen
      (packet.entry.capacity.trans s.capacity) (valid ⟨1,by decide⟩) (valid ⟨12,by decide⟩)
      sourceLive (congrArg LocalState.layout sourceCell) (congrArg LocalState.value destCell) (congrArg LocalState.layout destCell)
      facts.clocks packet.flags.ghost packet.flags.shallow (by rw [packet.flags.addresses];exact s.cachedAddress) packet.buffer packet.flags.race
      metadata uncached (by change packet.entry.output.child.tree.nodes.size+2 < 65536; have h:=packet.entry.growth;omega) (by change packet.entry.output.child.tree.nodes.size+2 ≤ 4294967295; have h:=packet.entry.growth;omega) (by omega)
      rfl budget dispatch s.source (valid ⟨11,by decide⟩) (congrArg LocalState.value lenCell) (congrArg LocalState.layout lenCell)
      packet.flags.backend packet.flags.unchecked packet.flags.noGc packet.flags.fixed thread active top both activity
      n (UInt64.pos_iff_ne_zero.mpr nonzeroCount) within packet.ready.size
      (congrArg LocalState.value thirteenCell) (congrArg LocalState.layout thirteenCell)
      (congrArg LocalState.value zeroCell) (congrArg LocalState.layout zeroCell)
      (congrArg LocalState.value sevenCell) (congrArg LocalState.layout sevenCell)
      (congrArg LocalState.value fifteenCell) (congrArg LocalState.layout fifteenCell)
      (congrArg LocalState.value sixteenCell) (congrArg LocalState.layout sixteenCell)
      (congrArg LocalState.value eightCell) (congrArg LocalState.layout eightCell)
      (congrArg LocalState.value nineCell) (congrArg LocalState.layout nineCell)
      (congrArg LocalState.value tenCell) (congrArg LocalState.layout tenCell) packet.ready.immediate
  have currentMemory : current.memory = initial.memory := by
    unfold current RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields s.options () (s.remaining+1) s.span).terminators]
  have finalMemory : post.memory = RetagEntry.updatedMemory initial.memory s.id buffer tree := by rw [memoryAfter,currentMemory]
  have finalFlags : GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.before post := {
    ghost := runtime.ghost
    shallow := runtime.shallow
    race := runtime.race
    addresses := runtime.addresses.trans packet.flags.addresses
    types := runtime.types.trans packet.flags.types
    extras := runtime.extras.trans packet.flags.extras
    backend := runtime.backend
    unchecked := runtime.unchecked
    noGc := runtime.noGc
    fixed := runtime.fixed
    active := runtime.active }
  have finalFrame : GeneralBorrowFreshRootScopedPhaseFrame.Frame (caller s n) result := {
    body := frame.body.trans packet.shape.body
    identity := frame.identity.trans packet.shape.identity
    callee := frame.callee.trans packet.shape.callee
    extra := frame.extra.trans packet.shape.extra
    returnPlace := frame.returnPlace.trans packet.shape.returnPlace
    continuation := frame.continuation.trans packet.shape.continuation
    varargs := frame.varargs.trans packet.shape.vaList
    localsIdentity := frame.localsIdentity.trans packet.shape.localsIdentity }
  change GeneralBorrowFreshRootScopedSharedToLenLedger.Graph packet.entry.output.child.tree tree packet.input.selected (global s) held at graph
  simp only [packet.parent,packet.selected,packet.maximum] at owner activityAfter graph
  exact ⟨{
    entry:=packet.entry,frame:=result,post:=post,trace:=SuccessfulTrace.append packet.trace trace,tree:=tree,tracker:=held,memory:=finalMemory,
    tracked:=trackedAfter,mode:=modeAfter.trans s.mode,formed:=runtimeAfter,owner:=owner,activity:=activityAfter,graph:=graph,flags:=finalFlags,
    metadata:=finalFrame,track:=track.trans packet.shape.track,location:=location,size:=size,source:=source.trans packet.ready.source,
    count:=count.trans packet.ready.countSlot,flag:=flag,temp15:=temp15,temp16:=temp16,
    high:=fun index low highBound => (high index low).trans (facts.high index low highBound),immediate:=immediate,zero:=zero.trans facts.zero }⟩
end
end DuplicatePrefix.GeneralBorrowRawWildcardWindowAccepted
