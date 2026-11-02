import duplicate_prefix.GenericFunctionEntrySharedBundle
import duplicate_prefix.PositiveRootEntryMetadata

namespace DuplicatePrefix.GenericFunctionEntryFullReady
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

set_option autoImplicit false in
structure Facts (frame : CompilerFrameContext.ActualFrame) (place : MPlaceTy Provenance) : Prop where
  entry : PositiveRootEntryMetadata.Shape frame place
  unused : ∀ index (valid : index < frame.locals.size), 17 ≤ index → frame.locals[index] = ⟨.dead,none⟩

set_option autoImplicit false in
/-- Export the return, relevance and remaining local-storage facts implicit in
the genuine installed frame and preserved by the actual nonzero-count prefix. -/
theorem from_shape
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) (race : before.dataRace = none)
    (adjusted : Immediate Provenance) (count : UInt64)
    (buffer : AllocId) (bufferChild : BorTag) (slot : AllocId) (slotChild : BorTag)
    (result : CompilerFrameContext.ActualFrame)
    (shape : GenericFunctionEntryPrefix.Shape
      (PositiveRootInstalledFrame.installed (RawRootInvocation.root before place race) adjusted count {} buffer bufferChild slot slotChild)
      result count) : Facts result place := by
  let raw := RawRootInvocation.root before place race
  let frame := PositiveRootInstalledFrame.installed raw adjusted count {} buffer bufferChild slot slotChild
  have initial := PositiveRootEntryMetadata.installed before place race adjusted count buffer bufferChild slot slotChild
  have entry : PositiveRootEntryMetadata.Shape result place := by
    refine ⟨shape.body.trans initial.body,shape.identity.trans initial.identity,shape.callee.trans initial.callee,
      (congrArg (·.dataRace) shape.extra).trans initial.noClocks,shape.continuation.trans initial.continuation,
      shape.vaList.trans initial.varargs,shape.slot0.trans initial.zero,shape.returnPlace.trans initial.returnPlace,
      shape.track.trans initial.trackNone,?_⟩
    rw [shape.extra]
    exact initial.relevant
  refine ⟨entry,?_⟩
  intro index valid high
  have bound : index < 25 := by rw [shape.size] at valid;exact valid
  have stored := PositiveRootInstalledFrame.slot_option raw (RawRootInvocation.locals before place race)
    adjusted count {} buffer bufferChild slot slotChild ⟨index,bound⟩
  have n0 : 0 ≠ index := by omega
  have n1 : 1 ≠ index := by omega
  have n2 : 2 ≠ index := by omega
  have n6 : 6 ≠ index := by omega
  have n13 : 13 ≠ index := by omega
  have n14 : 14 ≠ index := by omega
  have initialSlot : frame.locals[index]? = some ⟨.dead,none⟩ := by
    simpa only [Fin.val_mk,n0,n1,n2,n6,n13,n14,false_or,ite_false] using stored
  have finalSlot := (shape.keep index (by omega)).trans initialSlot
  simpa only [Array.getElem?_eq_getElem valid,Option.some.injEq] using finalSlot

end DuplicatePrefix.GenericFunctionEntryFullReady
