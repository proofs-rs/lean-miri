import duplicate_prefix.GeneralBorrowRawRootCurrentRelease
import duplicate_prefix.GeneralBorrowRawRootBoolReturn
namespace DuplicatePrefix.GeneralBorrowRawRootCurrentBoolReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Concurrency
open PhysicalMachineWrite
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- CURRENT phase facts and original slot metadata. The slot's current lookup,
real release plan, physical write and terminal success are all derived below. -/
structure Input where
  options : EvalConfigurationCore.Options
  limits : ExecutionMachine.Limits
  remaining : Nat
  span : PreparedContracts.FixedSpanQuery
  fuel : Nat
  debugOff : options.place.debugAssertions = false
  validationFuel : options.limits.validation = fuel+1
  context : Context
  validationContext : Context
  accessEq : (PreparedContracts.actualConfig options () remaining span).access = validationContext.access
  validationWidth : validationContext.pointers.arithmetic = ⟨Size.ofBytes 8⟩
  validationRuntimeSize : validationContext.access.runtime.pointerSize = Size.ofBytes 8
  sameRuntime : validationContext.access.runtime.base = context.access.runtime.base
  width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩
  runtimeWidth : context.access.runtime.base.pointerWidth = .w64
  runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8
  outerAccessEq : (PreparedContracts.actualConfig options () (remaining+1) span).access = context.access
  before : CompilerFrameContext.ActualFrame
  size : before.locals.size=25
  location : before.location=.mir ⟨10,0⟩
  value : Bool
  slot0 : before.locals[0]?=some ⟨.live (.immediate (.scalar (.fromBool value))),some RootCompilerFacts.boolLayout⟩
  immediate : CopyHelperCleanup.AllImmediate before
  body : before.body = RootBody.reflected.body.body
  identity : before.bodyIdentity = RootBody.reflected.body.identity
  callee : before.functionInstance = RootBody.reflected.functionInstance
  noLocalClocks : before.extra.dataRace = none
  continuation : before.returnContinuation = .stop true
  varargs : before.vaList = #[]
  machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  tracker : MachineHooks.BorrowState
  tracked : machine.borrowTracker = some tracker
  noClocks : machine.dataRace = none
  noBackend : machine.user.payload.payload.user.backend = .none
  ghost : machine.user.payload.ghost = false
  shallow : machine.user.payload.validation = .Shallow
  unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false
  noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0
  fixed : machine.threads.fixedScheduling = true
  thread : ThreadRecord
  active : machine.threads.activeThread? = some thread
  baseline : MemoryState Provenance BorrowTree MiriMemoryKind
  id : AllocId
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  tree : BorrowTree
  memoryEq : machine.memory = RetagEntry.updatedMemory baseline id entry tree
  tag : BorTag
  anchor : UniIndex
  selected : UniIndex
  maximum : Option BorTag
  offset : UInt64
  len : UInt64
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global
  positive : DuplicatePrefixBorrowAuthorization.Positive tree tracker.global.protectedTags
    (some anchor) (some selected) maximum offset len
  node : TreeNode
  present : tree.nodeAt anchor = some node
  sameTag : node.tag = tag
  hidden : node.isExposed = false
  distinct : tree.roots.toList.Nodup
  order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree
  short : tree.nodes.size < 65536
  activity : GeneralBorrowFreshActiveWithin.ActiveWithin tree anchor .Write offset (offset+len)
  slotId : AllocId
  separate : slotId ≠ id
  slot : LocalAllocation Provenance BorrowTree MiriMemoryKind
  slotBefore : baseline.live.find? (fun row => row.1 == slotId) = some (slotId,slot)
  slotRoot : BorTag
  slotChild : BorTag
  slotTree : slot.allocation.extra = PhysicalMachineWrite.slotTree slotRoot slotChild 1 true
  slotRootFree : tracker.global.protectedTags.contains slotRoot = false
  slotChildHeld : tracker.global.protectedTags.contains slotChild = true
  slotDistinct : slotRoot ≠ slotChild
  frameTracked : before.extra.borrowTracker = some
    ((({} : FrameState).addProtector id tag).addProtector slotId slotChild)
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
  cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == slotId) = some ⟨slotId,slotBase⟩
  extras : (context.extras.get machine.user).allocations.find? (fun row => row.1 == slotId) = some (slotId,⟨none,#[]⟩)
  destination : before.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩

/-- Concrete physical return input and its proved actual execution. The source
state/configuration/value and return-slot identities agree with the current
phase packet; no client supplies this execution proof as a precondition. -/
structure Outcome (input : Input) where
  physical : GeneralBorrowRawRootBoolReturn.Input
  options : physical.options = input.options
  limits : physical.limits = input.limits
  remaining : physical.remaining = input.remaining
  span : physical.span = input.span
  context : physical.context = input.context
  before : physical.before = input.before
  machine : physical.machine = input.machine
  value : physical.value = input.value
  slotId : physical.release.slotId = input.slotId
  slot : physical.release.slot = input.slot
  slotRoot : physical.release.slotRoot = input.slotRoot
  slotChild : physical.release.slotChild = input.slotChild
  returned : GeneralBorrowRawRootBoolReturn.Result physical

/-- Build both current release and physical-input records internally, then
execute the actual Bool ROOT return for either value. Current owner permissions
and the whole-heap relation are phase data; future safety is the conclusion. -/
theorem complete (input : Input) : Nonempty (Outcome input) := by
  obtain ⟨release,idEq,tagEq,anchorEq,bufferEq,slotIdEq,slotEq,slotRootEq,slotChildEq,frameEq⟩ :=
    GeneralBorrowRawRootCurrentRelease.form input.baseline input.machine.memory input.id input.slotId input.entry input.slot input.tree input.tracker.global
      input.memoryEq input.tag input.anchor input.selected input.maximum input.offset input.len input.runtime input.positive
      input.node input.present input.sameTag input.hidden input.distinct input.order input.short input.activity input.separate
      input.slotBefore input.slotRoot input.slotChild input.slotTree input.slotRootFree input.slotChildHeld input.slotDistinct
  let physical : GeneralBorrowRawRootBoolReturn.Input := {
    options := input.options,limits := input.limits,remaining := input.remaining,span := input.span,
    fuel := input.fuel,debugOff := input.debugOff,validationFuel := input.validationFuel,
    context := input.context,validationContext := input.validationContext,accessEq := input.accessEq,
    validationWidth := input.validationWidth,validationRuntimeSize := input.validationRuntimeSize,sameRuntime := input.sameRuntime,
    width := input.width,runtimeWidth := input.runtimeWidth,runtimeSize := input.runtimeSize,outerAccessEq := input.outerAccessEq,
    before := input.before,size := input.size,location := input.location,value := input.value,slot0 := input.slot0,
    immediate := input.immediate,body := input.body,identity := input.identity,callee := input.callee,
    noLocalClocks := input.noLocalClocks,continuation := input.continuation,varargs := input.varargs,
    machine := input.machine,tracker := input.tracker,tracked := input.tracked,noClocks := input.noClocks,noBackend := input.noBackend,
    ghost := input.ghost,shallow := input.shallow,unchecked := input.unchecked,noGc := input.noGc,fixed := input.fixed,
    thread := input.thread,active := input.active,release := release,
    frameTracked := by rw [frameEq];exact input.frameTracked,
    slotSize := by rw [slotEq];exact input.slotSize,
    slotStorage := by rw [slotEq];exact input.slotStorage,
    slotMask := by rw [slotEq];exact input.slotMask,
    slotProvenance := by rw [slotEq];exact input.slotProvenance,
    slotMutable := by rw [slotEq];exact input.slotMutable,
    place := input.place,layout := input.layout,slotBase := input.slotBase,
    slotPointer := by rw [slotIdEq,slotRootEq];exact input.slotPointer,
    aligned := input.aligned,fits := input.fits,
    cached := by rw [slotIdEq];exact input.cached,
    extras := by rw [slotIdEq];exact input.extras,
    destination := input.destination }
  exact ⟨{
    physical := physical,options := rfl,limits := rfl,remaining := rfl,span := rfl,context := rfl,
    before := rfl,machine := rfl,value := rfl,slotId := slotIdEq,slot := slotEq,slotRoot := slotRootEq,slotChild := slotChildEq,
    returned := GeneralBorrowRawRootBoolReturn.complete physical }⟩
end DuplicatePrefix.GeneralBorrowRawRootCurrentBoolReturn
