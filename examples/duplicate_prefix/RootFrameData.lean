import duplicate_prefix.RootEntryFrame
import duplicate_prefix.RootArgumentEntry

namespace DuplicatePrefix.RootFrameData
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- Structural facts carried by the real root frame throughout argument setup. -/
structure RootFrame where
  frame : Frame Provenance LocalLayout MachineHooks.FrameExtra
  size : frame.locals.size = 25
  body : frame.body = RootBody.reflected.body.body
  identity : frame.bodyIdentity = RootBody.reflected.body.identity
  callee : frame.functionInstance = RootBody.reflected.functionInstance
  noClocks : frame.extra.dataRace = none

theorem RootFrame.valid (root : RootFrame) (id : Fin 25) : id.val < root.frame.locals.size := by
  rw [root.size]
  exact id.isLt

noncomputable def raw (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (destination : RuntimeStackPlace Provenance) (identity : LocalsIdentity) (race : machine.dataRace = none) : RootFrame where
  frame := CallEntryFacts.rawRootFrame machine destination identity
  size := by rw [RootEntryFrame.raw_locals]; rfl
  body := (RootEntryFrame.raw_body machine destination identity).1
  identity := (RootEntryFrame.raw_body machine destination identity).2.1
  callee := (RootEntryFrame.raw_body machine destination identity).2.2
  noClocks := RootEntryFrame.raw_no_race machine destination identity race

noncomputable def atSpan (root : RootFrame) (span : SpanRef) : RootFrame where
  frame := {root.frame with location := .unwinding span}
  size := root.size
  body := root.body
  identity := root.identity
  callee := root.callee
  noClocks := root.noClocks

noncomputable def cache (root : RootFrame) (id : Fin 25) (layout : LocalLayout) : RootFrame where
  frame := LocalOperands.cachedLayoutFrame root.frame id.val layout (root.valid id)
  size := by simpa only [LocalOperands.cachedLayoutFrame, Array.size_set] using root.size
  body := root.body
  identity := root.identity
  callee := root.callee
  noClocks := root.noClocks

noncomputable def write (root : RootFrame) (id : Fin 25) (value : Immediate Provenance) : RootFrame where
  frame := {root.frame with locals := (root.frame.locals.set id.val
    {value := .live (.immediate value), layout := (root.frame.locals[id.val]'(root.valid id)).layout} (root.valid id))}
  size := by simpa only [Array.size_set] using root.size
  body := root.body
  identity := root.identity
  callee := root.callee
  noClocks := root.noClocks

noncomputable def live (root : RootFrame) (id : Fin 25) : RootFrame := write root id .uninit

theorem live_eq (root : RootFrame) (id : Fin 25) :
    (live root id).frame = RootArgumentEntry.liveFrame root.frame id.val (root.valid id) := rfl

end DuplicatePrefix.RootFrameData
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.RootFrameData.raw, ``DuplicatePrefix.RootFrameData.cache,
      ``DuplicatePrefix.RootFrameData.write, ``DuplicatePrefix.RootFrameData.live_eq] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved root frame data dependency {dependency}"
