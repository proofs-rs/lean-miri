import empty_function.CanonicalProtectionTotal
import empty_function.LocalIndirectPhasesNoUB
import empty_function.PushedSnapshot
namespace EmptyFunction.CanonicalLocalProtection
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxHeartbeats 8000000

theorem outcome (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (_runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.LocalDestination s p input.tracker)
    (old : MemPlace Provenance) (indirect : destination.oldOperand = .indirect old)
    (entry : LocalIndirectPhasesNoUB.Prefix s metadata p input destination old) :
    ProtectionOutcome.Outcome s ⟨LocalIndirectPrefix.selectedPlace old destination.offset,s.abi.ret.layout⟩
      (LocalCachedPush.cachedState s p input.tracker destination entry.older entry.bound).stack.frames
      {entry.frame with location := .unwinding metadata.localSpan} entry.machine := by
  obtain ⟨previous,pushed⟩ := entry.pushed
  have snapshots := PushedSnapshot.fields s metadata p.before.machine
    (LocalCachedPush.cachedState s p input.tracker destination entry.older entry.bound).stack.frames entry.frame previous
  have memory : entry.machine.memory = p.before.machine.memory := by rw [pushed];exact snapshots.1
  have addresses : entry.machine.user.addresses = p.before.machine.user.addresses := by rw [pushed];exact snapshots.2.1
  have compiler : entry.machine.user.payload.payload.user.runtime = p.before.machine.user.payload.payload.user.runtime := by
    rw [pushed];exact snapshots.2.2
  have effective := LocalIndirectPrefix.effective s p input.tracker destination old indirect
  have noMeta : (LocalIndirectPrefix.selectedPlace old destination.offset).metadata = .none := by
    cases offset : destination.offset with
    | none => exact (destination.oldRepresentation old indirect).1
    | some amount => rfl
  have aligned : (LocalIndirectPrefix.selectedPlace old destination.offset).misaligned = none := by
    cases offset : destination.offset with
    | none => exact (destination.oldRepresentation old indirect).2
    | some amount => exact (destination.oldRepresentation old indirect).2
  let place : ProtectionPlace.Input s p.before input.tracker :=
    ⟨⟨LocalIndirectPrefix.selectedPlace old destination.offset,s.abi.ret.layout⟩,rfl,noMeta,aligned,input.effective _ effective⟩
  exact CanonicalProtectionTotal.protect s metadata profile p input place effective _
    {entry.frame with location := .unwinding metadata.localSpan} entry.machine entry.machineTracker
    entry.borrowed memory addresses compiler entry.noRace

end EmptyFunction.CanonicalLocalProtection
