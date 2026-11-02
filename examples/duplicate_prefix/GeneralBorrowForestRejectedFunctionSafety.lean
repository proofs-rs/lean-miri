import duplicate_prefix.GeneralBorrowForestRejectedMachineAssembly
import duplicate_prefix.GeneralBorrowForestRejectedTreeBuild
namespace DuplicatePrefix.GeneralBorrowForestRejectedFunctionSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open ActualReferenceContext GenericFunctionEntryState GeneralBorrowForestRejectedMachineAssembly
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
attribute [local irreducible] GeneralBorrowForestEntrySharedInput.build GeneralBorrowForestRejectedTreeBuild.build GeneralBorrowForestRejectedTreeData.tree
set_option autoImplicit false in
/-- Original caller-tree resources for the positive rejected-count whole ROOT
invocation. Tags, allocator and permission hygiene are INITIAL data; neither a
post-entry tree nor a successful operation/release/return is supplied. -/
structure Initial extends toMachine : GeneralBorrowForestRejectedMachineAssembly.Initial where
  allocator : GeneralBorrowGcAllocator.Invariant entry.allocation.extra
  room : entry.allocation.extra.nodes.size+6 ≤ 4294967295
  vacantClean : GeneralBorrowGcVacantClean.VacantClean entry.allocation.extra
  exprFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping (held tracker fresh slotFresh).global.nextPointerTag
  helperFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping
    (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag
  rootExprDifferent : tracker.global.nextPointerTag ≠ (held tracker fresh slotFresh).global.nextPointerTag
  rootHelperDifferent : tracker.global.nextPointerTag ≠
    (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag

def Result (s : Initial) : Prop :=
  let input := s.toMachine
  let cfg := config s.options (s.remaining+1) s.span
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨cfg,s.limits,fun _ _ => True⟩
  ∃ (slot : Allocation Provenance BorrowTree) (physical : GeneralBorrowForestRootRejectedPhysical.Input)
    (returned : Allocation Provenance BorrowTree),
    let initial := Storage.withCurrent #[] (entryFrame input) (entryMachine input slot)
    let done := CanonicalCopy.replaceAllocation (GeneralBorrowForestRootRejectedPhysical.popped physical)
      physical.release.slotId physical.release.slot.kind returned
    Call.initStackFrame (ExecutionMachine.callHooks cfg s.limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
        (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
        ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ = .ok () initial ∧
    SuccessfulTrace.Trace cfg s.limits initial done ∧
    ExecutionMachine.step cfg s.limits () done = (done,.ok false) ∧
    CallSafety.NoUBBeforeReturn safety 1 initial ∧
    target_bytes physical.context.access.runtime.base physical.release.slot.allocation.byteSize 0 = .ok (AllocationCopy.snapshot returned)

def firstInput (s : Initial) : GeneralBorrowForestRejectedMachineAssembly.First s.toMachine := by
  let input := s.toMachine
  have bounds : s.offset.toNat+s.len.toNat ≤ s.entry.allocation.extra.locations.size.bytes.toNat := by
    rw [s.capacity];exact s.bounds
  exact GeneralBorrowForestEntrySharedInput.build s.entry.allocation.extra s.tracker s.parentTag s.offset s.len
    (UInt64.pos_iff_ne_zero.mp s.positive) s.data bounds s.clean s.fresh s.slotFresh s.successorFresh s.successorDifferent
    s.allocator s.room s.vacantClean (entryTracker input).global.nextPointerTag
    (ReferenceBorrowDriver.allocatedTracker (entryTracker input) s.fresh3).global.nextPointerTag
    s.exprFresh s.rootExprDifferent s.helperFresh s.rootHelperDifferent

def treeInput (s : Initial) : GeneralBorrowForestRejectedMachineAssembly.TreeData s.toMachine (firstInput s) := by
  let input := s.toMachine
  exact GeneralBorrowForestRejectedTreeBuild.build (entryTree input) (entryTracker input) s.fresh3 s.tracker.global.nextPointerTag
    (GeneralBorrowFreshMetadataChildMutableSlot.index s.data.slot) s.data.primary s.data.extras s.offset s.len (firstInput s)
    (UInt64.pos_iff_ne_zero.mp s.positive) s.exprUnheld

attribute [local irreducible] firstInput treeInput

/-- Actual original protected ROOT call, complete positive count>len/2 body,
physical false return and terminal scoped NoUB for every permitted finite
Unit-choice prefix. Arbitrary multiple-root initial histories are represented
by the explicit original caller graph/ownership/allocator/cache contracts. -/
theorem invoke (s : Initial) : Result s := by
  let input := s.toMachine
  obtain ⟨slot,boundary,options,limits,remaining,span,call,prefixTrace⟩ := GeneralBorrowForestRejectedMachineAssembly.prepare input (firstInput s) (treeInput s)
  obtain ⟨physical,returned,physicalOptions,physicalLimits,physicalRemaining,physicalSpan,suffixTrace,terminal,_,bytes⟩ :=
    GeneralBorrowForestRejectedAfterLenSafety.invoke boundary
  have suffix := suffixTrace
  simp only [options,limits,remaining,span] at suffix
  have trace := SuccessfulTrace.append prefixTrace suffix
  have terminal' := terminal
  simp only [options,limits,remaining,span] at terminal'
  let cfg := config s.options (s.remaining+1) s.span
  let initial := Storage.withCurrent #[] (entryFrame input) (entryMachine input slot)
  let done := CanonicalCopy.replaceAllocation (GeneralBorrowForestRootRejectedPhysical.popped physical)
    physical.release.slotId physical.release.slot.kind returned
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨cfg,s.limits,fun _ _ => True⟩
  have entry : CallSafety.IsCallEntry 1 initial := ⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 done := by change 0<1;decide
  have safe := SuccessfulTrace.no_ub safety 1 initial done entry trace past
  exact ⟨slot,physical,returned,call,trace,terminal',safe,bytes⟩
end
end DuplicatePrefix.GeneralBorrowForestRejectedFunctionSafety
