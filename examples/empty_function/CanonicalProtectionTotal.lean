import empty_function.CanonicalResolutionUniform
import empty_function.ProtectionPlace
import empty_function.CanonicalLiveProtection
import empty_function.ProtectionSmallTotal
namespace EmptyFunction.CanonicalProtectionTotal
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem protect (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (place : ProtectionPlace.Input s p.before input.tracker)
    (effective : InputDraft.effectivePointer p = some place.place.mplace.ptr)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F) (before : ProtectionOutcome.Machine)
    (enabled : before.borrowTracker = some input.tracker)
    (frameBorrow : frame.extra.borrowTracker = some {})
    (memory : before.memory = p.before.machine.memory)
    (addresses : before.user.addresses = p.before.machine.user.addresses)
    (runtime : before.user.payload.payload.user.runtime = p.before.machine.user.payload.payload.user.runtime)
    (noRace : before.dataRace = none) :
    ProtectionOutcome.Outcome s place.place frames frame before := by
  obtain ⟨answer,uniform,hit⟩ := CanonicalResolutionUniform.resolve s metadata p input _ effective
  have resolve := fun global => uniform
    (LocalUnit.current frames frame (ProtectionSmallTotal.allocatedMachine before input.tracker global))
    memory addresses
  cases answer with
  | none =>
    exact ProtectionSmallTotal.unresolved s metadata profile place.place frames frame before input.tracker
      enabled frameBorrow place.layout place.sizedMetadata place.alignmentCache resolve
  | some location =>
    rcases location with ⟨id,⟨offset⟩,parent⟩
    rcases hit with ⟨selected,backing⟩
    cases classified : before.memory.getAllocInfo id with
    | error error =>
      exact ProtectionSmallTotal.resolved_info_error s metadata profile place.place frames frame before
        input.tracker enabled frameBorrow place.layout id offset parent resolve error classified
    | ok info =>
      by_cases data : info.kind = .liveData
      · rcases ResourceFailures.tag_total input.tracker.global with ⟨maximum,failed⟩ |
          ⟨global,tagged,room,counter,roots,protectors,tracked⟩
        · exact ProtectionStops.maximum s metadata profile place.place frames frame before input.tracker
            place.layout enabled maximum
        · exact CanonicalLiveProtection.protect s metadata profile p input place.place
            place.layout place.sizedMetadata place.alignmentCache frames frame before enabled frameBorrow
            memory addresses runtime noRace effective global input.tracker.global.nextPointerTag tagged
            id offset parent (resolve global) info classified data selected backing
      · exact ProtectionSmallTotal.resolved_nondata s metadata profile place.place frames frame before
          input.tracker enabled frameBorrow place.layout place.sizedMetadata place.alignmentCache
          id offset parent resolve info classified data
end EmptyFunction.CanonicalProtectionTotal
