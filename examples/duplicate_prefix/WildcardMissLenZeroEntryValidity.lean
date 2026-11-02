import duplicate_prefix.WildcardMissRootZeroValidator
import duplicate_prefix.ProtectedZeroReferenceValidator
import duplicate_prefix.EmptyBorrowHelpers
import duplicate_prefix.RootReferenceInfo
import duplicate_prefix.ProtectorInsertion
import duplicate_prefix.ProtectedStages
namespace DuplicatePrefix.WildcardMissLenZeroEntryValidity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true


theorem validate
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (address : UInt64) (nonzero : address ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 SharedReferenceMetadata.sharedLayout).imm))
    (cached : frame.locals[localId].layout = some SharedReferenceMetadata.sharedLayout)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (miss : WildcardMissAddress.Miss machine.user.addresses address)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let resultMachine := ReferenceBorrowDriver.allocatedMachine machine tracker fresh
    ValidityMachine.validateRuntime cfg.validity () (validityFuel+1)
      (LocalPlaces.localRuntimePlace frames.size frame localId SharedReferenceMetadata.sharedLayout) true
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {frame with
          locals := frame.locals.set localId
            {value := .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 SharedReferenceMetadata.sharedLayout).imm),
             layout := frame.locals[localId].layout} valid} resultMachine) := by
  have info := RootReferenceInfo.facts options remaining span ctx true
  have result := WildcardMissRootZeroValidator.validate options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    SharedReferenceMetadata.sharedLayout .Not .FnEntry (sharedPolicy true) frozenRead
    (by decide +kernel) (shared_initial true) shared_entry_policy
    info.shape info.pointeeQuery info.unpin info.unsafeUnpin info.frozen info.dereference
    info.sized info.readable "&[u8]" info.named info.classified
    address nonzero frames frame machine tracker enabled mode
    fresh localId valid live cached ghost shallow addressMode miss metadata notConstructed
  exact result
end
end DuplicatePrefix.WildcardMissLenZeroEntryValidity
