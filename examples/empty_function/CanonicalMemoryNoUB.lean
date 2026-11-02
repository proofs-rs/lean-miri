import empty_function.CanonicalProtectionTotal
import empty_function.MemoryPhasesNoUB
import empty_function.PushedSnapshot
namespace EmptyFunction.CanonicalMemoryNoUB
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxHeartbeats 8000000

theorem noUB (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.MemoryDestination s p input.tracker) : CallLevelNoUB.NoUB s p := by
  apply MemoryPhasesNoUB.noUB s metadata profile p runtime input destination
  intro entry
  obtain ⟨previous,pushed⟩ := entry.pushed
  have snapshots := PushedSnapshot.fields s metadata p.before.machine p.before.stack.frames entry.frame previous
  have memory : entry.machine.memory = p.before.machine.memory := by rw [pushed];exact snapshots.1
  have addresses : entry.machine.user.addresses = p.before.machine.user.addresses := by rw [pushed];exact snapshots.2.1
  have compiler : entry.machine.user.payload.payload.user.runtime = p.before.machine.user.payload.payload.user.runtime := by
    rw [pushed];exact snapshots.2.2
  let place : ProtectionPlace.Input s p.before input.tracker :=
    ⟨destination.place,destination.layout,destination.sizedMetadata,destination.alignmentCache,destination.pointer⟩
  have effective : InputDraft.effectivePointer p = some destination.place.mplace.ptr := by
    simp [InputDraft.effectivePointer,destination.encoding]
  exact CanonicalProtectionTotal.protect s metadata profile p input place effective p.before.stack.frames
    {entry.frame with location := .unwinding metadata.localSpan} entry.machine entry.machineTracker entry.borrowed
    memory addresses compiler entry.noRace
end EmptyFunction.CanonicalMemoryNoUB
