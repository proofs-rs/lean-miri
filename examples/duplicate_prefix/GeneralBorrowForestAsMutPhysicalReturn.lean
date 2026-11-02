import duplicate_prefix.GeneralBorrowForestAsMutBodyToCopy
import duplicate_prefix.GeneralBorrowForestCopyReturn
import duplicate_prefix.GeneralBorrowForestAsMutReleaseData
import duplicate_prefix.GeneralBorrowForestAsMutProtectorWeakens
import duplicate_prefix.GeneralBorrowFreshRestoreData
import duplicate_prefix.SuccessfulTraceTerminal

namespace DuplicatePrefix.GeneralBorrowForestAsMutPhysicalReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Concurrency
open PhysicalMachineWrite DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

set_option autoImplicit false in
/-- Initial initialized-helper data. Root-copy inputs and all subsequent
runtime successes are constructed internally, not assumed at PC8:4. -/
structure Input where
  start : GeneralBorrowForestAsMutBodyToCopy.Input
  statementFuel : start.limits.validation = start.fuel+1
  releaseLower : start.release.lower = start.offset
  releaseUpper : start.release.upper = start.offset+start.len
  capacity : start.entry.allocation.extra.locations.size = start.entry.allocation.byteSize
  target : UniIndex
  targetNode : TreeNode
  targetPresent : start.entry.allocation.extra.nodeAt target = some targetNode
  targetNotExposed : targetNode.isExposed = false
  targetTag : BorTag
  targetTagPresent : start.entry.allocation.extra.indexOfTag targetTag = some target
  covered : GeneralBorrowGraph.RootsCover start.entry.allocation.extra
  targetContext : GeneralBorrowForestAccessData.Context start.entry.allocation.extra target start.release.primary start.release.extras
  targetRootPath : ∀ location, ((source_normal_projection start.entry.allocation.extra location start.tracker.global.protectedTags).topology.ancestorPath target.toNat).getLast! = start.release.primary.toNat
  targetWithin : GeneralBorrowFreshActiveWithin.ActiveWithin start.entry.allocation.extra target .Write start.offset (start.offset+start.len)
  subset : ∀ location : LocationTree,
    ∀ position ∈ (source_normal_projection start.entry.allocation.extra location start.tracker.global.protectedTags).topology.ancestorPath target.toNat,
      position ∈ (source_normal_projection start.entry.allocation.extra location start.tracker.global.protectedTags).topology.ancestorPath start.release.anchor.toNat
  escaping : ∀ (location : LocationTree) (index : UniIndex) (node : TreeNode), start.entry.allocation.extra.nodeAt index = some node →
    index.toNat ∈ (source_normal_projection start.entry.allocation.extra location start.tracker.global.protectedTags).topology.ancestorPath start.release.anchor.toNat →
    index.toNat ∉ (source_normal_projection start.entry.allocation.extra location start.tracker.global.protectedTags).topology.ancestorPath target.toNat →
    start.tracker.global.protectedTags.contains node.tag = false ∨ ∃ allocation : AllocId,
      (allocation,node.tag) ∈ ((({} : FrameState).addProtector start.id start.tag).protectedTags.toList)
  storage : start.entry.allocation.len = start.entry.allocation.byteSize.bytes.toNat
  maskValid : InitMaskCopy.WellFormed start.entry.allocation.initializationMask
  maskLength : start.entry.allocation.initializationMask.len = start.entry.allocation.byteSize
  initialized : InitMaskCopy.InitializedOn start.entry.allocation.initializationMask (Size.ofBytes start.offset) (Size.ofBytes (start.offset+start.count))
  provenance : ProvenanceCopy.WellFormed start.entry.allocation.provenanceMap start.entry.allocation.len
  storageFits : start.entry.allocation.len+64 < 18446744073709551616
  mutable : start.entry.allocation.mutability = .Mut
  bufferExtras : start.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == start.id) = some (start.id,⟨none,#[]⟩)
  bounded : start.count ≤ (PreparedContracts.actualConfig start.options () (start.remaining+1) start.span).projection.maxSizeOfVal.bytes
  zero : start.caller.locals[0]? = some ⟨.live (.immediate .uninit),none⟩
  continuation : start.caller.returnContinuation = .stop true
  varargs : start.caller.vaList = #[]
  context : Context
  validationContext : Context
  accessEq : (PreparedContracts.actualConfig start.options () start.remaining start.span).access = validationContext.access
  validationWidth : validationContext.pointers.arithmetic = ⟨Size.ofBytes 8⟩
  validationRuntimeSize : validationContext.access.runtime.pointerSize = Size.ofBytes 8
  sameRuntime : validationContext.access.runtime.base = context.access.runtime.base
  width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩
  runtimeWidth : context.access.runtime.base.pointerWidth = .w64
  runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8
  outerAccessEq : (PreparedContracts.actualConfig start.options () (start.remaining+1) start.span).access = context.access
  slotId : AllocId
  separate : slotId ≠ start.id
  slot : LocalAllocation Provenance BorrowTree MiriMemoryKind
  slotPresent : start.machine.memory.live.find? (fun row => row.1 == slotId) = some (slotId,slot)
  slotRoot : BorTag
  slotChild : BorTag
  slotTree : slot.allocation.extra = slotTree slotRoot slotChild 1 true
  slotRootFree : start.tracker.global.protectedTags.contains slotRoot = false
  slotChildHeld : start.tracker.global.protectedTags.contains slotChild = true
  slotDistinct : slotRoot ≠ slotChild
  slotChildNotHelper : slotChild ≠ start.tag
  frameTracked : start.caller.extra.borrowTracker = some
    ((({} : FrameState).addProtector start.id targetTag).addProtector slotId slotChild)
  slotSize : slot.allocation.byteSize = Size.ofBytes 1
  slotStorage : slot.allocation.len = 1
  slotMask : slot.allocation.initializationMask = InitMask.new (Size.ofBytes 1) false
  slotProvenance : slot.allocation.provenanceMap = ProvenanceMap.new
  slotMutable : slot.allocation.mutability = .Mut
  place : MPlaceTy Provenance
  layout : place.layout = RootCompilerFacts.boolLayout
  slotBase : UInt64
  slotPointer : place.mplace.ptr = Pointer.new (some (.concrete slotId slotRoot)) (Size.ofBytes slotBase)
  aligned : place.mplace.misaligned = none
  fits : slotBase.toNat + 1 < 2^64
  cached : start.machine.user.addresses.baseAddr.find? (fun row => row.allocId == slotId) = some ⟨slotId,slotBase⟩
  extras : start.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == slotId) = some (slotId,⟨none,#[]⟩)
  destination : start.caller.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩


def Result (input : Input) : Prop :=
  let start := input.start
  let config := PreparedContracts.actualConfig start.options () (start.remaining+1) start.span
  let initial := Storage.withCurrent #[start.caller] (GeneralBorrowForestAsMutBodyToCopy.helper start) start.machine
  ∃ finalState updated,
    SuccessfulTrace.Trace config start.limits initial finalState ∧
    ExecutionMachine.step config start.limits () finalState = (finalState,.ok false) ∧
    finalState.stack.frames = #[] ∧
    finalState.machine.memory.live.find? (fun row => row.1 == input.slotId) = some (input.slotId,⟨input.slot.kind,updated⟩) ∧
    updated.extra = parentWrittenTree input.slotRoot input.slotChild 1 ∧
    updated.byteSize = input.slot.allocation.byteSize ∧ updated.len = input.slot.allocation.len ∧
    updated.initializationMask = InitMask.new input.slot.allocation.byteSize true ∧ updated.provenanceMap = ProvenanceMap.new ∧
    target_bytes input.context.access.runtime.base input.slot.allocation.byteSize 1 = .ok (AllocationCopy.snapshot updated) ∧
    updated.mutability = input.slot.allocation.mutability ∧
    ∀ before, SuccessfulTrace.Trace config start.limits initial before →
      ∃ after continuing, ExecutionMachine.step config start.limits () before = (after,.ok continuing)

/-- Complete the actual initialized-helper, copy and physical true return.
Every successful finite Unit-choice prefix, including after the helper pop,
is proved free of all interpreter errors. -/
theorem complete (input : Input) : Result input := by
  let s := input.start
  let held := GeneralBorrowForestAsMutBodyToCopy.held s
  let rawTree := s.entry.allocation.extra
  let released := GeneralBorrowForestAsMutReleasePlan.release rawTree s.tracker.global.protectedTags s.tag
  have lower : s.release.lower = s.offset := input.releaseLower
  have upper : s.release.upper = s.offset+s.len := input.releaseUpper
  have cap : rawTree.locations.size = s.entry.allocation.byteSize := input.capacity
  have data := GeneralBorrowForestAsMutReleaseData.release rawTree s.tracker.global.protectedTags s.tag s.release.anchor s.release.primary s.release.extras
    s.release.lower s.release.upper s.release.positive s.release.fits s.release.context s.release.tagPresent s.release.within s.release.owned s.release.well input.target
    s.offset (s.offset+s.len) (by rw [lower];exact Nat.le_refl _) (by rw [upper];exact Nat.le_refl _) input.targetWithin
  obtain ⟨map,same,well,capacity⟩ := data.2.1
  change released.tree = {rawTree with locations := map} at same
  have nodes : released.tree.nodes = rawTree.nodes := by
    have known := congrArg BorrowTree.nodes same
    exact known
  have releasedWell : released.tree.locations.WellFormed := by rw [same];exact well
  have releasedSize : released.tree.locations.size = rawTree.locations.size := by rw [same];exact capacity
  have owned : OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data released.tree location held.global.protectedTags s.release.anchor s.release.primary s.release.extras))
      s.offset (s.offset+s.len) released.tree.locations := by
    have releasedOwned : OwnedOn
        (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data released.tree location s.tracker.global.protectedTags s.release.anchor s.release.primary s.release.extras))
        s.offset (s.offset+s.len) released.tree.locations := by
      simpa only [released,GeneralBorrowForestAsMutReleasePlan.release,lower,upper] using data.2.2.2
    intro position valid positive start stop
    obtain ⟨localData⟩ := releasedOwned position valid positive start stop
    exact ⟨GeneralBorrowForestAsMutProtectorWeakens.location released.tree _ s.tracker.global.protectedTags held.global.protectedTags
      (GeneralBorrowRelease.end_call_weakens s.tracker.global (({} : FrameState).addProtector s.id s.tag))
      s.release.anchor s.release.primary s.release.extras localData⟩
  have initialRestore := GeneralBorrowFreshRestoreData.end_call rawTree s.tracker.global (({} : FrameState).addProtector s.id s.tag)
    s.release.anchor input.target input.targetNode input.targetPresent input.subset input.escaping
  have afterRestore := GeneralBorrowFreshRestoreData.before_context rawTree s.tracker.global.protectedTags held.global.protectedTags
    held.global.protectedTags s.release.anchor input.target initialRestore
  have restore : GeneralBorrowFreshLifetimeRestore.RestoreTo released.tree held.global.protectedTags held.global.protectedTags
      s.release.anchor input.target (fun _ => true) := by
    rw [same]
    exact GeneralBorrowFreshLifetimeRestore.restore_map rawTree map _ _ _ _ _ afterRestore
  have twice := (PositiveRootCopyBounds.guarded s.len s.count s.offset s.entry.allocation.byteSize.bytes s.within s.bounds).2.1
  let borrow : GeneralBorrowForestCopyInput.Input released.tree held.global.protectedTags s.tag s.offset s.len s.count := {
    anchor := s.release.anchor,primary := s.release.primary,extras := s.release.extras,fits := by rw [nodes];exact s.release.fits
    context := by rw [same];exact GeneralBorrowForestForeignSliceRepeated.context_on_map rawTree map s.release.anchor s.release.primary s.release.extras s.release.context
    covered := by rw [same];exact input.covered
    tagPresent := by rw [same];exact s.release.tagPresent
    well := releasedWell,bounds := by rw [releasedSize,cap];exact s.bounds
    twice := twice,owned := owned }
  obtain ⟨caller,machine,trace,shape,memory,tracked,race,ghost,shallow,backend,addresses,types,extras,active,fixed,unchecked,noGc⟩ :=
    GeneralBorrowForestAsMutBodyToCopy.run s
  let destination : Scalar Provenance := Scalar.fromPointer (PreparedContracts.actualConfig s.options () (s.remaining+1) s.span).access.runtime.base
    (Pointer.new (.concrete s.id s.tag) (Size.ofBytes (s.base+s.offset+s.count)))
  have bound (index : Nat) (small : index < 25) : index < caller.locals.size := by rw [shape.size];exact small
  have cell {index : Nat} (valid : index < caller.locals.size) {row : LocalState Provenance LocalLayout}
      (known : caller.locals[index]? = some row) : caller.locals[index]'valid = row :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans known)
  have row18 := cell (bound 18 (by decide)) shape.slot18
  have row19 := cell (bound 19 (by decide)) shape.slot19
  have row21 := cell (bound 21 (by decide)) shape.slot21
  have row24 := cell (bound 24 (by decide)) shape.slot24
  let entry : CopyRootEntry.Input s.options s.limits s.remaining s.span #[] caller machine
      (GeneralBorrowForestAsMutBodyToCopy.pointer s) destination s.count := {
    debug := s.debug,tracker := held,tracked := tracked,valid := bound 18 (by decide),old := .uninit
    live := congrArg (fun row => row.value) row18,uncached := congrArg (fun row => row.layout) row18
    noClocks := (congrArg (fun extra => extra.dataRace) shape.extra).trans s.clocks
    noRace := race,body := shape.body.trans s.body,identity := shape.identity.trans s.identity,callee := shape.callee.trans s.callee
    trackNone := shape.trackedCaller.trans s.track,location := shape.location,fuel := s.fuel,validationFuel := s.validation
    ghost := ghost,shallow := shallow,thread := s.thread,active := active,top := s.top,relevant := by rw [shape.extra];exact s.relevant
    budget := s.budget,budgetEq := s.dispatch,backend := backend,unchecked := unchecked,noGc := noGc,fixed := fixed,source := s.source,cmp := s.cmp
    valid19 := bound 19 (by decide),valid21 := bound 21 (by decide),valid24 := bound 24 (by decide)
    live19 := congrArg (fun row => row.value) row19,cache19 := congrArg (fun row => row.layout) row19
    live21 := congrArg (fun row => row.value) row21,cache21 := congrArg (fun row => row.layout) row21
    live24 := congrArg (fun row => row.value) row24,cache24 := congrArg (fun row => row.layout) row24 }
  have bufferPresent : machine.memory.live.find? (fun row => row.1 == s.id) = some (s.id,{s.entry with allocation := s.entry.allocation.setExtra released.tree}) := by
    rw [memory]
    exact StackPopRelease.lookup_commit_same s.machine.memory s.id s.entry released.tree
  let copy : GeneralBorrowForestCopyRootGuardBody.CopyData s.options s.remaining s.span machine held (GeneralBorrowForestAsMutBodyToCopy.pointer s) destination s.count := {
    id := s.id,tag := s.tag,base := s.base,offset := s.offset,sliceLen := s.len,kind := s.entry.kind
    allocation := s.entry.allocation.setExtra released.tree
    positive := s.countPositive,sliceBounds := s.bounds,copyBounds := twice,storage := input.storage,maskValid := input.maskValid
    maskLen := input.maskLength,initialized := input.initialized,valid := input.provenance,storageFits := input.storageFits,mutable := input.mutable
    extras := by rw [extras];exact input.bufferExtras
    live := bufferPresent,cached := by rw [addresses];exact s.cachedAddress
    borrow := borrow,bounded := input.bounded,source := rfl,destination := by dsimp only [destination];rw [UInt64.add_assoc] }
  have slotPresent : machine.memory.live.find? (fun row => row.1 == input.slotId) = some (input.slotId,input.slot) := by
    rw [memory]
    exact StackPopRelease.lookup_commit_other s.machine.memory s.id input.slotId s.entry input.slot released.tree input.separate input.slotPresent
  have slotRootFree : held.global.protectedTags.contains input.slotRoot = false := by
    change (s.tracker.global.endCall (({} : FrameState).addProtector s.id s.tag)).protectedTags.contains input.slotRoot = false
    rw [StackPopRelease.end_call_contains]
    split
    · rfl
    · exact input.slotRootFree
  have slotChildHeld : held.global.protectedTags.contains input.slotChild = true := by
    change (s.tracker.global.endCall (({} : FrameState).addProtector s.id s.tag)).protectedTags.contains input.slotChild = true
    have different : input.slotChild ≠ s.tag := input.slotChildNotHelper
    rw [StackPopRelease.end_call_contains]
    simpa only [FrameState.addProtector,Array.toList_push,Array.toList_empty,List.nil_append,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,
      or_false,different,↓reduceIte] using input.slotChildHeld
  let completeInput : GeneralBorrowForestCopyReturn.Input := {
    options := s.options,limits := s.limits,remaining := s.remaining,span := s.span,before := s.caller,caller := caller,machine := machine
    pointer := GeneralBorrowForestAsMutBodyToCopy.pointer s,destinationValue := destination,count := s.count,entry := entry,data := copy
    statementFuel := input.statementFuel,defaultMode := s.mode
    context := input.context,validationContext := input.validationContext,accessEq := input.accessEq,validationWidth := input.validationWidth
    validationRuntimeSize := input.validationRuntimeSize,sameRuntime := input.sameRuntime,width := input.width,runtimeWidth := input.runtimeWidth
    runtimeSize := input.runtimeSize,outerAccessEq := input.outerAccessEq,shape := shape,zero := input.zero,body := s.body,identity := s.identity,callee := s.callee
    noLocalClocks := s.clocks,continuation := input.continuation,varargs := input.varargs
    slotId := input.slotId,separate := input.separate,slot := input.slot,slotPresent := slotPresent,slotRoot := input.slotRoot,slotChild := input.slotChild
    slotTree := input.slotTree,slotRootFree := slotRootFree,slotChildHeld := slotChildHeld,slotDistinct := input.slotDistinct
    release := {
      copy := borrow,target := input.target,active := data.2.2.1,restore := restore,
      targetContext := by change GeneralBorrowForestAccessData.Context released.tree input.target s.release.primary s.release.extras;rw [same];exact GeneralBorrowForestForeignSliceRepeated.context_on_map rawTree map input.target s.release.primary s.release.extras input.targetContext,
      targetRootPath := by intro location;change ((source_normal_projection released.tree location held.global.protectedTags).topology.ancestorPath input.target.toNat).getLast! = s.release.primary.toNat;rw [same];exact input.targetRootPath location}
    releaseTag := input.targetTag,releaseNode := input.targetNode,releaseNodePresent := by change released.tree.nodeAt input.target = some input.targetNode;rw [same];exact input.targetPresent
    releaseNotExposed := input.targetNotExposed,releaseTagPresent := by change released.tree.indexOfTag input.targetTag = some input.target;rw [same];exact input.targetTagPresent
    frameTracked := input.frameTracked,slotSize := input.slotSize,slotStorage := input.slotStorage,slotMask := input.slotMask
    slotProvenance := input.slotProvenance,slotMutable := input.slotMutable,place := input.place,layout := input.layout,slotBase := input.slotBase
    slotPointer := input.slotPointer,aligned := input.aligned,fits := input.fits,cached := by rw [addresses];exact input.cached
    extras := by rw [extras];exact input.extras,destination := input.destination }
  obtain ⟨done,updated,copyTrace,terminal,safe,empty,slotLookup,written,size,length,mask,provenance,encoding,mutable⟩ := GeneralBorrowForestCopyReturn.complete completeInput
  have full := SuccessfulTrace.append trace copyTrace
  exact ⟨done,updated,full,terminal,empty,slotLookup,written,size,length,mask,provenance,encoding,mutable,
    SuccessfulTraceTerminal.prefix_step_success full terminal⟩

end DuplicatePrefix.GeneralBorrowForestAsMutPhysicalReturn
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.GeneralBorrowForestAsMutPhysicalReturn.complete) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved initialized mutable-helper physical return dependency {dependency}"
