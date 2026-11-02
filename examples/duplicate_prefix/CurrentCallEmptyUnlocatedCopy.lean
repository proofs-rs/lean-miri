import duplicate_prefix.CurrentCallEmptyConcreteResources
import duplicate_prefix.S03WildcardMissArgumentCopy

/-! Integer and actual wildcard-query-miss empty arguments create no source
node or protector. The real copy advances the tag allocator and retains the
Bool resource on exactly that copy's post-machine. -/
namespace DuplicatePrefix.CurrentCallEmptyUnlocatedCopy
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open ActualReferenceMetadata
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

theorem advance {before : Before} {tracker : MachineHooks.BorrowState} {data : Identities}
    {owner : Nat} {id : AllocId} {offset : Nat}
    (B : UniformWindow before tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (post : Before) (memoryEq : post.memory = before.memory) :
    ∃ Q : UniformWindow post {tracker with global := GeneralBorrowFnEntryRegistration.advanced tracker.global room}
        data owner id offset 1 .ret,
      Q.pointer = B.pointer ∧ Q.allocation = B.allocation ∧ Q.precise = B.precise ∧
      DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra
        (GeneralBorrowFnEntryRegistration.advanced tracker.global room) := by
  have present : Present (ActualWorld post) id B.allocation := by
    simpa only [ActualWorld,memoryEq] using B.present
  have issued := CurrentCallAllocationLicense.spatial B.issued post
    {tracker with global := GeneralBorrowFnEntryRegistration.advanced tracker.global room} B.allocation present
    (by rfl) rfl rfl rfl (by intro position root slot;exact slot)
    (by intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩)
    B.precise.completion (by intro root origin edge;exact edge)
  let Q : UniformWindow post {tracker with global := GeneralBorrowFnEntryRegistration.advanced tracker.global room}
      data owner id offset 1 .ret := {B with present := present,issued := issued}
  refine ⟨Q,rfl,rfl,rfl,⟨runtime.formed,runtime.coherent,runtime.possible,?_⟩⟩
  apply GeneralBorrowForestTagHighWaterHistory.weaken B.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag
    (TypedRetagEmpty.successorTag tracker.global.nextPointerTag room) runtime.below
  rw [GenericFunctionEntryNumerics.successor_value]
  omega

theorem integer
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut = false)
    (implicitWrites : options.retag.implicitWrites = false)
    (debugOff : options.place.debugAssertions = false)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (validationEq : options.limits.validation = validityFuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : MIR.LocalId) (old : Immediate Provenance) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some reference)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (address : UInt64) (nonzero : address ≠ 0)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (data : Identities) (owner : Nat) (id : AllocId) (offset : Nat)
    (B : UniformWindow machine tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId reference) :
    let value := (RetagReferencePlace.integerSliceValue address 0 reference).imm
    let copiedFrame := {frame with locals := (frame.locals.set localId
      {value := .live (.immediate value),layout := frame.locals[localId].layout} valid)}
    let post := TypedRetagEmpty.afterTag (Storage.withCurrent frames copiedFrame machine) tracker fresh
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyAllowTransmute ()
      ⟨.immediate (RetagReferencePlace.integerSliceValue address 0 reference).imm, reference⟩ view
      (Storage.withCurrent frames frame machine) = .ok ()
      (TypedRetagEmpty.afterTag (Storage.withCurrent frames {frame with locals := (frame.locals.set localId
        {value := .live (.immediate (RetagReferencePlace.integerSliceValue address 0 reference).imm),
         layout := frame.locals[localId].layout} valid)} machine) tracker fresh) ∧
      ∃ Q : UniformWindow post.machine {tracker with global := GeneralBorrowFnEntryRegistration.advanced tracker.global fresh}
          data owner id offset 1 .ret,
        Q.pointer = B.pointer ∧ Q.allocation = B.allocation ∧ Q.precise = B.precise ∧
        DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra
          (GeneralBorrowFnEntryRegistration.advanced tracker.global fresh)
 := by
  dsimp only
  refine ⟨ReferenceArgumentCopy.copy_empty_argument options limits remaining span cmp precise implicitWrites debugOff dynamicFuel validityFuel fuelEq validationEq
    frames frame machine localId old valid live cached noClocks ghost shallow address nonzero tracker enabled mode fresh metadata notConstructed view destination,?_⟩
  exact advance B runtime fresh _ rfl


theorem wildcard_miss
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut = false)
    (implicitWrites : options.retag.implicitWrites = false)
    (debugOff : options.place.debugAssertions = false)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (validationEq : options.limits.validation = validityFuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : MIR.LocalId) (old : Immediate Provenance) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some reference)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (address : UInt64) (nonzero : address ≠ 0)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (miss : machine.user.addresses.allocIdFromAddr address 0
      (GlobalAddressLiveErrorExclusion.lookup machine.memory) = .ok none)
    (data : Identities) (owner : Nat) (id : AllocId) (offset : Nat)
    (B : UniformWindow machine tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId reference) :
    let value := (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
      (Pointer.new .wildcard (Size.ofBytes address)) 0 reference).imm
    let copiedFrame := {frame with locals := (frame.locals.set localId
      {value := .live (.immediate value),layout := frame.locals[localId].layout} valid)}
    let post := TypedRetagEmpty.afterTag (Storage.withCurrent frames copiedFrame machine) tracker fresh
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyAllowTransmute ()
      ⟨.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference).imm, reference⟩ view
      (Storage.withCurrent frames frame machine) = .ok ()
      (TypedRetagEmpty.afterTag (Storage.withCurrent frames {frame with locals := (frame.locals.set localId
        {value := .live (.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference).imm),
         layout := frame.locals[localId].layout} valid)} machine) tracker fresh) ∧
      ∃ Q : UniformWindow post.machine {tracker with global := GeneralBorrowFnEntryRegistration.advanced tracker.global fresh}
          data owner id offset 1 .ret,
        Q.pointer = B.pointer ∧ Q.allocation = B.allocation ∧ Q.precise = B.precise ∧
        DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra
          (GeneralBorrowFnEntryRegistration.advanced tracker.global fresh)
 := by
  dsimp only
  refine ⟨S03WildcardMissArgumentCopy.copy_empty_argument options limits remaining span cmp precise implicitWrites debugOff dynamicFuel validityFuel fuelEq validationEq
    frames frame machine localId old valid live cached noClocks ghost shallow address nonzero tracker enabled mode fresh addressMode miss metadata notConstructed view destination,?_⟩
  exact advance B runtime fresh _ rfl

end
end DuplicatePrefix.CurrentCallEmptyUnlocatedCopy
