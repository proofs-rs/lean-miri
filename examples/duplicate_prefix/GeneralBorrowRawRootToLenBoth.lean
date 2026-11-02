import duplicate_prefix.GeneralBorrowRawRootPrefixFrame
import duplicate_prefix.GeneralBorrowRawSharedToLenObserver
namespace DuplicatePrefix.GeneralBorrowRawRootToLenBoth
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState GeneralBorrowRawRootPrefixResources
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
abbrev Initial := GeneralBorrowRawRootZeroEntry.Initial

def refValue (s : Initial) : Immediate Provenance :=
  (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
    (Pointer.new (.concrete s.id (bufferGlobal s).nextPointerTag) (Size.ofBytes (s.base+s.offset)))
    s.len SharedReferenceMetadata.sharedLayout).imm

def lenFrame (s : Initial) (callerFrame : CompilerFrameContext.ActualFrame) (size : callerFrame.locals.size = 25) : CompilerFrameContext.ActualFrame :=
  let caller := GeneralBorrowForestSharedPreLenFrame.after callerFrame (by rw [size];decide) (refValue s)
  LenCallResultFrame.resultFrame caller (by
    simpa [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]
      using (show 11 < callerFrame.locals.size by rw [size];decide)) s.len

structure Outcome (s : Initial) (callerFrame : CompilerFrameContext.ActualFrame)
    (initial : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (frame : CompilerFrameContext.ActualFrame) (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) where
  prefixSize : callerFrame.locals.size = 25
  frameEq : frame = lenFrame s callerFrame prefixSize
  tree : BorrowTree
  tracker : MachineHooks.BorrowState
  child : UniIndex
  memory : post.memory = RetagEntry.updatedMemory initial.memory s.id s.entry tree
  tracked : post.borrowTracker = some tracker
  mode : tracker.retagMode = .Default
  formed : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global
  owner : Nonempty (GeneralBorrowReadRowRange.Positive tree tracker.global.protectedTags child s.raw.selected s.raw.maximum s.offset s.len)
  observer : UniIndex
  original : Nonempty (DuplicatePrefixBorrowAuthorization.Positive tree tracker.global.protectedTags
    (some observer) (some s.raw.selected) s.raw.maximum s.offset s.len)
  originalActivity : GeneralBorrowFreshActiveWithin.ActiveWithin tree observer .Write s.offset (s.offset+s.len)
  runtime : GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.before post

/-- Original call-time state executes initialization, the positive-count pure
callerFrame, the actual shared Ref, len call, real release and helper return. The ORIGINAL mutable owner Both/activity and all
current frame/metadata/cache/thread facts are derived. Only initial settings
and the stated remaining node/tag/dispatch resources are added. -/
theorem executes (s : Initial) (n : UInt64) (positiveCount : n ≠ 0)
    (preciseOff : s.options.retag.preciseInteriorMut = false)
    (implicitOff : s.options.retag.implicitWrites = false)
    (budget : Nat) (dispatch : s.limits.callDispatch = budget+1)
    (nodeMargin : s.entry.allocation.extra.nodes.size+3 < 65536)
    (tagMargin : s.tracker.global.nextPointerTag.value.toNat+3 < 18446744073709551615) :
    ∃ (entryFrame callerFrame result : CompilerFrameContext.ActualFrame)
      (initial post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      GeneralBorrowRawRootPositivePrefix.ActualCall s n entryFrame initial ∧
      entryFrame = GeneralBorrowRawRootInitialize.caller s n ∧
      SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits (Storage.withCurrent #[] entryFrame initial)
        (Storage.withCurrent #[] result post) ∧
      GenericFunctionEntryPrefix.Shape entryFrame callerFrame n ∧ Nonempty (Outcome s callerFrame initial result post) := by
  obtain ⟨entryFrame,callerFrame,initial,call,initialEq,pureTrace,shape,resources⟩ :=
    GeneralBorrowRawRootPrefixResources.executes s n positiveCount
  have facts := GeneralBorrowRawRootPrefixFrame.of_shape s n entryFrame callerFrame initialEq shape
  let current := RootZeroCompleteState.tick s.options s.remaining s.span initial
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {s.entry with allocation := s.entry.allocation.setExtra (bufferTree s)}
  let tracker := held s.tracker s.fresh s.slotFresh
  have tagRoom : (bufferGlobal s).nextPointerTag.value.toNat+1 < 18446744073709551615 := by
    have first := GenericFunctionEntryNumerics.successor_value s.tracker.global.nextPointerTag s.fresh
    have second := GenericFunctionEntryNumerics.successor_value (next s.tracker s.fresh).global.nextPointerTag s.slotFresh
    change (next s.tracker s.fresh).global.nextPointerTag.value.toNat = s.tracker.global.nextPointerTag.value.toNat+1 at first
    change (bufferGlobal s).nextPointerTag.value.toNat = (next s.tracker s.fresh).global.nextPointerTag.value.toNat+1 at second
    omega
  have fresh : (bufferGlobal s).nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (bufferGlobal s).nextPointerTag.value.toNat < 18446744073709551615
    omega
  obtain ⟨parent,tagged,⟨owner⟩,activity⟩ := resources.owner
  obtain ⟨readOwner⟩ := GeneralBorrowReadRowRange.of_positive (bufferTree s) (bufferGlobal s).protectedTags parent s.raw.selected s.raw.maximum s.offset s.len owner
  let raw : GeneralBorrowRawShared.Input (bufferTree s) (bufferGlobal s) := {
    parentTag:=s.tracker.global.nextPointerTag,parent:=parent,selected:=s.raw.selected,maximum:=s.raw.maximum,offset:=s.offset,len:=s.len,
    tagged:=tagged,positive:=readOwner,distinct:=by rw [resources.roots];exact s.raw.distinct,
    order:=resources.order,short:=resources.short,nodeRoom:=by have h:=resources.short;omega,tagRoom:=fresh}
  have valid1 : (1 : MIR.LocalId) < callerFrame.locals.size := by rw [facts.size];decide
  have valid12 : (RootReferenceFacts.destination true) < callerFrame.locals.size := by change 12 < callerFrame.locals.size;rw [facts.size];decide
  have valid11 : 11 < callerFrame.locals.size := by rw [facts.size];decide
  have sourceCell := Option.some.inj ((Array.getElem?_eq_getElem valid1).symm.trans facts.source)
  have destCell := Option.some.inj ((Array.getElem?_eq_getElem valid12).symm.trans facts.dest)
  have lenCell := Option.some.inj ((Array.getElem?_eq_getElem valid11).symm.trans facts.len)
  have present : current.memory.live.find? (fun row => row.1 == s.id) = some (s.id,entry) := by
    rw [resources.memory];exact resources.buffer
  have cached : current.user.addresses.baseAddr.find? (fun row => row.allocId == s.id) = some ⟨s.id,s.base⟩ := by
    rw [resources.runtime.addresses];exact s.cachedAddress
  have metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] callerFrame current)).metadata = PreparedReflection.actual.runtime := by
    change current.user.payload.payload.user.types.metadata = _
    rw [resources.runtime.types];exact s.metadata
  have notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] callerFrame current)).entries.any (·.value.ty == 4) = false := by
    change current.user.payload.payload.user.types.entries.any (·.value.ty == 4) = _
    rw [resources.runtime.types];exact s.notConstructed
  have shortRoom : (bufferTree s).nodes.size+2 < 65536 := by have h:=resources.growth;omega
  have nodeRoom : (bufferTree s).nodes.size+2 ≤ 4294967295 := by have h:=resources.short;omega
  obtain ⟨thread,active,top⟩ := resources.runtime.active
  obtain ⟨result,post,finalTree,postTracker,child,lenTrace,resultEq,memoryEq,trackerEq,modeEq,runtimeAfter,positiveAfter,originalBoth,originalActivity,
    ghostAfter,shallowAfter,raceAfter,addresses,types,extras,backend,unchecked,noGc,fixed,threadAfter⟩ :=
    GeneralBorrowRawSharedToLenObserver.complete s.options s.limits s.remaining s.span preciseOff implicitOff s.debugOff s.cmp
      s.dynamicFuel s.validityFuel s.fuelEq s.validationEq s.base s.offset s.len s.id entry s.positive s.nonzero s.signedFits
      #[] callerFrame current facts.body facts.identity facts.callee facts.location tracker resources.tracker s.mode fresh
      s.tracker.global.nextPointerTag resources.formed raw rfl rfl rfl (resources.capacity.trans s.capacity)
      valid1 valid12
      (by simpa only [GeneralBorrowRawRootPrefixFrame.sourceValue,ActualReferenceContext.config,CanonicalConfigFacts.actual_access_runtime] using congrArg LocalState.value sourceCell)
      (congrArg LocalState.layout sourceCell) (congrArg LocalState.value destCell) (congrArg LocalState.layout destCell)
      facts.clocks resources.runtime.ghost resources.runtime.shallow cached present resources.runtime.race metadata notConstructed
      shortRoom nodeRoom tagRoom rfl budget dispatch s.source valid11 (congrArg LocalState.value lenCell)
      (congrArg LocalState.layout lenCell) resources.runtime.backend resources.runtime.unchecked resources.runtime.noGc
      resources.runtime.fixed thread active top owner activity
  have finalMemory : post.memory = RetagEntry.updatedMemory initial.memory s.id s.entry finalTree := by
    rw [memoryEq,resources.memory]
    rfl
  have finalFlags : GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.before post :=
    ⟨ghostAfter,shallowAfter,raceAfter,addresses.trans resources.runtime.addresses,types.trans resources.runtime.types,
      extras.trans resources.runtime.extras,backend,unchecked,noGc,fixed,threadAfter⟩
  refine ⟨entryFrame,callerFrame,result,initial,post,call,initialEq,SuccessfulTrace.append pureTrace lenTrace,shape,?_⟩
  exact ⟨{
    prefixSize:=facts.size,frameEq:=resultEq,tree:=finalTree,tracker:=postTracker,child:=child,memory:=finalMemory,
    tracked:=trackerEq,mode:=modeEq.trans s.mode,formed:=runtimeAfter,owner:=positiveAfter,observer:=parent,original:=originalBoth,
    originalActivity:=originalActivity,runtime:=finalFlags}⟩
end
end DuplicatePrefix.GeneralBorrowRawRootToLenBoth
