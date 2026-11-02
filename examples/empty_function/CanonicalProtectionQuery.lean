import empty_function.CanonicalResolutionUniform
import empty_function.ProtectionPlace
import empty_function.CanonicalLiveProtectionQuery
import empty_function.SmallProtectionSnapshot
import empty_function.ProtectionInfoError
import empty_function.InitialQueryTransport
import empty_function.ProtectionSmallTotal
namespace EmptyFunction.CanonicalProtectionQuery
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem query (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (place : ProtectionPlace.Input s p.before input.tracker)
    (effective : InputDraft.effectivePointer p = some place.place.mplace.ptr)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F) (before : ProtectionOutcome.Machine)
    (enabled : before.borrowTracker = some input.tracker)
    (frameBorrow : frame.extra.borrowTracker = some {})
    (memory : before.memory = p.before.machine.memory)
    (addresses : before.user.addresses = p.before.machine.user.addresses)
    (runtime : before.user.payload.payload.user.runtime = p.before.machine.user.payload.payload.user.runtime)
    (noRace : before.dataRace = none)
    (afterState : State)
    (actual : TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag place.place
      (LocalUnit.current frames frame before) = .ok () afterState)
    (destination : InputDraft.LocalDestination s p input.tracker)
    (old : MemPlace Provenance) (indirect : destination.oldOperand = .indirect old)
    (amount : Size) (projected : destination.offset = some amount) (positive : amount.bytes ≠ 0) :
    EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers afterState old amount .inbounds .none =
      .ok (ProjectedIndirectPreflight.shifted old amount) := by
  obtain ⟨answer,uniform,hit⟩ := CanonicalResolutionUniform.resolve s metadata p input _ effective
  have resolve := fun global => uniform
    (LocalUnit.current frames frame (ProtectionSmallTotal.allocatedMachine before input.tracker global))
    memory addresses
  cases answer with
  | none =>
    obtain ⟨keptMemory,keptAddresses⟩ := SmallProtectionSnapshot.unresolved s metadata profile place.place frames frame before input.tracker
      enabled frameBorrow place.layout place.sizedMetadata place.alignmentCache resolve afterState actual
    exact InitialQueryTransport.query s metadata p input.tracker destination old indirect amount projected afterState
      (keptMemory.trans memory) (keptAddresses.trans addresses)
  | some location =>
    rcases location with ⟨id,⟨offset⟩,parent⟩
    rcases hit with ⟨selected,backing⟩
    cases classified : before.memory.getAllocInfo id with
    | error error =>
      exact False.elim (ProtectionInfoError.info_error_impossible s metadata profile place.place frames frame before
        input.tracker enabled frameBorrow place.layout id offset parent resolve error classified afterState actual)
    | ok info =>
      by_cases data : info.kind = .liveData
      · rcases ResourceFailures.tag_total input.tracker.global with ⟨maximum,failed⟩ |
          ⟨global,tagged,room,counter,roots,protectors,tracked⟩
        · obtain ⟨reason,failedActual⟩ := ResourceFailures.protect_maximum_failure s.cfg.retag s.limits.retag place.place
            (LocalUnit.current frames frame before) input.tracker _
            ((CanonicalUnitRetag.fields s metadata profile).size place.place place.layout) enabled maximum
          rw [actual] at failedActual
          cases failedActual
        · exact CanonicalLiveProtectionQuery.query s metadata profile p input place.place
            place.layout place.sizedMetadata place.alignmentCache frames frame before enabled frameBorrow
            memory addresses runtime noRace effective global input.tracker.global.nextPointerTag tagged
            id offset parent (resolve global) info classified data selected backing
            afterState actual destination old indirect amount projected positive
      · obtain ⟨keptMemory,keptAddresses⟩ := SmallProtectionSnapshot.resolved_nondata s metadata profile place.place frames frame before
          input.tracker enabled frameBorrow place.layout place.sizedMetadata place.alignmentCache
          id offset parent resolve info classified data afterState actual
        exact InitialQueryTransport.query s metadata p input.tracker destination old indirect amount projected afterState
          (keptMemory.trans memory) (keptAddresses.trans addresses)
end EmptyFunction.CanonicalProtectionQuery
