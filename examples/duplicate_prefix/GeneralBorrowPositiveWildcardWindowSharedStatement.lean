import duplicate_prefix.GeneralBorrowExposedScopedWritableSharedStatement
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowSharedPreLenFrame
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowSharedStatement
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext RootReferenceInfo RootReferenceTrees
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- The positive wildcard physical prefix's Ready shape and initial leaf
resources derive the real next shared-expression step and all pre-length locals. -/
theorem executes_from_ready
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (base offset len : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (input : GeneralBorrowFreshMetadataChildShared.Input)
    (selected head : UniIndex) (tail : List UniIndex) (writable : Nat → Bool)
    (raw : GeneralBorrowExposedScopedWritableSharedConstructor.Resources input tracker.global.protectedTags selected head tail writable)
    (treeEq : input.tree = entry.allocation.extra)
    (tagEq : input.newTag = tracker.global.nextPointerTag)
    (offsetEq : input.offset = offset) (lenEq : input.len = len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (count : UInt64) (borrowFrame : FrameState)
    (ready : GeneralBorrowPositiveWildcardWindowFunctionToShared.Ready frame
      (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id input.parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm count borrowFrame)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let value := RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout true)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry (GeneralBorrowForestMixedShared.child entry.allocation.extra tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag false offset len .VisitChildrenOfAccessed).tree}
    ∃ valid : 12 < frame.locals.size,
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
        (Storage.withCurrent frames frame machine) =
        (Storage.withCurrent frames (GeneralBorrowForestSharedPreLenFrame.after frame valid value.imm) resultMachine,.ok true) ∧
      GeneralBorrowForestSharedPreLenFrame.Facts frame
        (GeneralBorrowForestSharedPreLenFrame.after frame valid value.imm) count value.imm := by
  have valid1 : (1 : MIR.LocalId) < frame.locals.size := by rw [ready.size];decide
  have valid12 : (12 : MIR.LocalId) < frame.locals.size := by rw [ready.size];decide
  have source := ready.source
  rw [Array.getElem?_eq_getElem valid1] at source
  have sourceRow := Option.some.inj source
  have dest := ready.exprSlot
  rw [Array.getElem?_eq_getElem valid12] at dest
  have destRow := Option.some.inj dest
  have step := GeneralBorrowExposedScopedWritableSharedStatement.executes options limits remaining span preciseOff implicitOff debugOff cmp
    dynamicFuel validityFuel fuelEq validationFuel base offset len id entry positive nonzero signedFits frames frame machine
    ready.body ready.identity ready.callee ready.location tracker enabled defaultMode fresh input selected head tail writable raw
    treeEq tagEq offsetEq lenEq capacity valid1 valid12 (congrArg (·.value) sourceRow) (congrArg (·.layout) sourceRow)
    (congrArg (·.value) destRow) (congrArg (·.layout) destRow) ready.noClocks ghost shallow cachedAddress present race metadata notConstructed
  dsimp only
  refine ⟨valid12,step,?_⟩
  exact GeneralBorrowPositiveWildcardWindowSharedPreLenFrame.build frame _ _ count borrowFrame ready valid12
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowSharedStatement
