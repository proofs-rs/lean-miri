import duplicate_prefix.S03SeparateReturnRegistration
import duplicate_prefix.S03LiveEmptyState

namespace DuplicatePrefix.S03SeparateEmptyArgument
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts RootFrameData EmptyRootArguments ActualReferenceContext ConcreteEmptyRootArguments
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Pure current-state transport for an allocation whose bytes and tree are
unchanged. The real transition below derives the lookup and permission fields. -/
def transport {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place) (after : Before)
    (tracker : MachineHooks.BorrowState) (enabled : after.borrowTracker = some tracker)
    (live : after.memory.live.find? (fun row => row.1 == original.id) = some (original.id,original.entry))
    (addresses : after.user.addresses = before.user.addresses)
    (positive : DuplicatePrefixBorrowAuthorization.Positive original.entry.allocation.extra tracker.global.protectedTags
      original.source original.selectedRoot original.maximum original.offset 1) :
    DuplicatePrefixReturnPlaceInput.Input after place := {
  tracker := tracker, enabled := enabled,
  pointer := original.pointer, physicalPointer := original.physicalPointer,
  layout := original.layout, aligned := original.aligned,
  id := original.id, entry := original.entry, base := original.base, offset := original.offset, capacity := original.capacity,
  live := live, cachedBase := by rw [addresses];exact original.cachedBase,
  pointerAddress := original.pointerAddress, nonnull := original.nonnull,
  addressFits := original.addressFits, bounds := original.bounds, size := original.size, bytes := original.bytes,
  mutable := original.mutable, maskValid := original.maskValid, maskLength := original.maskLength,
  provenanceMap := original.provenanceMap, borrowSize := original.borrowSize,
  source := original.source, selectedRoot := original.selectedRoot, maximum := original.maximum,
  binding := by rw [addresses];exact original.binding, borrow := positive }

/-- The other-allocation argument commit leaves the original concrete or
wildcard destination physically intact. Its fresh protector is absent from
all return-tree nodes; registration therefore preserves the full capability. -/
def input {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts original.entry.allocation.extra original.tracker.global)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (argumentId : AllocId) (argumentEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (parentTag : BorTag)
    (slot : ConcreteEmptyPoolEntry.Input argumentEntry.allocation.extra parentTag original.tracker.global.nextPointerTag)
    (separate : original.id ≠ argumentId) :
    DuplicatePrefixReturnPlaceInput.Input
      (ConcretePoolRootArgumentScope.resultMachine before original.tracker fresh argumentId argumentEntry parentTag slot) place := by
  let positive := Classical.choice (S03SeparateReturnRegistration.register original.entry.allocation.extra original.tracker.global
    argumentId fresh runtime original.source original.selectedRoot original.maximum original.offset 1 original.borrow).2.1
  exact transport original _ (S03LiveEmptyState.next original.tracker fresh) rfl
    (StackPopRelease.lookup_commit_other before.memory argumentId original.id argumentEntry original.entry
      slot.after separate original.live) rfl positive

/-- Full facts on the literal unchanged return tree. Activity, node exposure,
parent/tag metadata, order and hidden-frame facts need no reconstruction when
this input is used: its entry is definitionally the original allocation. -/
theorem facts {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts original.entry.allocation.extra original.tracker.global)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (argumentId : AllocId) :
    DuplicatePrefixBorrowContract.RuntimeFacts original.entry.allocation.extra (S03LiveEmptyState.next original.tracker fresh).global ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive original.entry.allocation.extra
      (S03LiveEmptyState.next original.tracker fresh).global.protectedTags
      original.source original.selectedRoot original.maximum original.offset 1) ∧
    ∀ index node, original.entry.allocation.extra.nodeAt index = some node →
      (S03LiveEmptyState.next original.tracker fresh).global.protectedTags.get node.tag =
        original.tracker.global.protectedTags.get node.tag :=
  S03SeparateReturnRegistration.register original.entry.allocation.extra original.tracker.global argumentId fresh runtime
    original.source original.selectedRoot original.maximum original.offset 1 original.borrow

/-- The initial raw push changes control/thread caches but preserves every
physical return-input projection. No argument retag or tag allocation occurs. -/
def rawInput {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place) :
    DuplicatePrefixReturnPlaceInput.Input (RawRootInvocation.machine #[] before) place :=
  transport original _ original.tracker original.enabled original.live rfl original.borrow

def argumentsMachine {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (argumentId : AllocId) (argumentEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (parentTag : BorTag)
    (slot : ConcreteEmptyPoolEntry.Input argumentEntry.allocation.extra parentTag original.tracker.global.nextPointerTag) :=
  ConcretePoolRootArgumentScope.resultMachine (RawRootInvocation.machine #[] before) original.tracker fresh
    argumentId argumentEntry parentTag slot

def after_raw_input {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts original.entry.allocation.extra original.tracker.global)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (argumentId : AllocId) (argumentEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (parentTag : BorTag)
    (slot : ConcreteEmptyPoolEntry.Input argumentEntry.allocation.extra parentTag original.tracker.global.nextPointerTag)
    (separate : original.id ≠ argumentId) :
    DuplicatePrefixReturnPlaceInput.Input (argumentsMachine original fresh argumentId argumentEntry parentTag slot) place :=
  input (rawInput original) runtime fresh argumentId argumentEntry parentTag slot separate

/-- Actual post-argument model on the exact separate-allocation state. -/
theorem model {options : EvalConfigurationCore.Options} {remaining : Nat}
    {span : PreparedContracts.FixedSpanQuery} {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (initial : DuplicatePrefixCallModel.Model options remaining span before)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (argumentId : AllocId) (argumentEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (parentTag : BorTag)
    (slot : ConcreteEmptyPoolEntry.Input argumentEntry.allocation.extra parentTag original.tracker.global.nextPointerTag) :
    DuplicatePrefixCallModel.Model options (remaining+1) span (argumentsMachine original fresh argumentId argumentEntry parentTag slot) := by
  have shifted := S03IntegerZeroState.retime initial (remaining+1)
  obtain ⟨tracker,enabled,mode⟩ := initial.defaultTracker
  have same : tracker = original.tracker := Option.some.inj (enabled.symm.trans original.enabled)
  subst tracker
  refine {shifted with defaultTracker := ⟨S03LiveEmptyState.next original.tracker fresh,rfl,mode⟩,unchecked := ?_,noGc := ?_}
  · change ((PreparedContracts.actualConfig options () (remaining+1+1) span).terminators.getControl
      (RawRootInvocation.machine #[] before).user).checkedArithmetic = false
    rw [RootZeroInvocationState.raw_control]
    exact shifted.unchecked
  · change ((PreparedContracts.actualConfig options () (remaining+1+1) span).terminators.getControl
      (RawRootInvocation.machine #[] before).user).gcInterval = 0
    rw [RootZeroInvocationState.raw_control]
    exact shifted.noGc

/-- Actual configured live empty argument operation with a distinct return
allocation. The complete original destination Input and RuntimeFacts survive
its source-order global registration and argument-tree commit. -/
theorem scope
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (tracker : MachineHooks.BorrowState)
    (base offset n : UInt64) (nonzero : base+offset ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (dead1 : (root.frame.locals[1]'(root.valid i1)).value = .dead)
    (cache1 : (root.frame.locals[1]'(root.valid i1)).layout = none)
    (dead2 : (root.frame.locals[2]'(root.valid i2)).value = .dead)
    (cache2 : (root.frame.locals[2]'(root.valid i2)).layout = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (borrowFrame : FrameState) (frameBorrow : root.frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (entryInput : ConcreteEmptyPoolEntry.Input entry.allocation.extra parentTag tracker.global.nextPointerTag)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (returnPlace : MPlaceTy Provenance)
    (returnInput : DuplicatePrefixReturnPlaceInput.Input machine returnPlace)
    (returnRuntime : DuplicatePrefixBorrowContract.RuntimeFacts returnInput.entry.allocation.extra returnInput.tracker.global)
    (separate : returnInput.id ≠ id) :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
        ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second n)) (Storage.withCurrent frames root.frame machine) =
      .ok (2,2) (Storage.withCurrent frames (RootArgumentsTwo.result (ConcreteEmptyRootArguments.firstDone root adjusted borrowFrame id tracker.global.nextPointerTag) n).frame
        (ConcretePoolRootArgumentScope.resultMachine machine tracker fresh id entry parentTag entryInput)) ∧
    ∃ next : DuplicatePrefixReturnPlaceInput.Input
        (ConcretePoolRootArgumentScope.resultMachine machine tracker fresh id entry parentTag entryInput) returnPlace,
      next.entry = returnInput.entry ∧ next.id = returnInput.id ∧ next.pointer = returnInput.pointer ∧
      next.offset = returnInput.offset ∧ next.source = returnInput.source ∧ next.selectedRoot = returnInput.selectedRoot ∧
      next.maximum = returnInput.maximum ∧
      DuplicatePrefixBorrowContract.RuntimeFacts next.entry.allocation.extra next.tracker.global := by
  have same : tracker = returnInput.tracker := Option.some.inj (enabled.symm.trans returnInput.enabled)
  subst tracker
  have actual := ConcretePoolRootArgumentScope.scope options limits remaining span ctx debugOff cmp
    dynamicFuel validityFuel fuelEq validationEq id parentTag returnInput.tracker base offset n nonzero entry frames root machine
    dead1 cache1 dead2 cache2 ghost shallow cachedAddress present borrowFrame frameBorrow enabled fresh entryInput metadata notConstructed
  let next := input returnInput returnRuntime fresh id entry parentTag entryInput separate
  refine ⟨actual,next,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  exact (facts returnInput returnRuntime fresh id).1

end
end DuplicatePrefix.S03SeparateEmptyArgument
