import duplicate_prefix.AddPush
import duplicate_prefix.RootArgumentEntry

namespace DuplicatePrefix.AddFrameData
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- Structural facts carried by the real root frame throughout argument setup. -/
structure RootFrame where
  frame : Frame Provenance LocalLayout MachineHooks.FrameExtra
  size : frame.locals.size = 5
  body : frame.body = HelperCompilerFacts.addBody.body
  identity : frame.bodyIdentity = HelperCompilerFacts.addBody.identity
  callee : frame.functionInstance = HelperCompilerFacts.addCall.callee
  noClocks : frame.extra.dataRace = none

theorem RootFrame.valid (root : RootFrame) (id : Fin 5) : id.val < root.frame.locals.size := by
  rw [root.size]
  exact id.isLt

noncomputable def raw (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (destination : RuntimeStackPlace Provenance) (cont : ReturnContinuation) (identity : LocalsIdentity)
    (race : machine.dataRace = none) : RootFrame where
  frame := TrackedFrame.raw HelperCompilerFacts.addCall.callee HelperCompilerFacts.addBody AddEntryFacts.addPreamble machine destination cont identity
  size := by with_unfolding_all rfl
  body := rfl
  identity := rfl
  callee := rfl
  noClocks := by simp only [TrackedFrame.raw, race, Option.map_none]

noncomputable def atSpan (root : RootFrame) (span : SpanRef) : RootFrame where
  frame := {root.frame with location := .unwinding span}
  size := root.size
  body := root.body
  identity := root.identity
  callee := root.callee
  noClocks := root.noClocks

noncomputable def cache (root : RootFrame) (id : Fin 5) (layout : LocalLayout) : RootFrame where
  frame := LocalOperands.cachedLayoutFrame root.frame id.val layout (root.valid id)
  size := by simpa only [LocalOperands.cachedLayoutFrame, Array.size_set] using root.size
  body := root.body
  identity := root.identity
  callee := root.callee
  noClocks := root.noClocks

noncomputable def write (root : RootFrame) (id : Fin 5) (value : Immediate Provenance) : RootFrame where
  frame := {root.frame with locals := (root.frame.locals.set id.val
    {value := .live (.immediate value), layout := (root.frame.locals[id.val]'(root.valid id)).layout} (root.valid id))}
  size := by simpa only [Array.size_set] using root.size
  body := root.body
  identity := root.identity
  callee := root.callee
  noClocks := root.noClocks

noncomputable def live (root : RootFrame) (id : Fin 5) : RootFrame := write root id .uninit

theorem live_eq (root : RootFrame) (id : Fin 5) :
    (live root id).frame = RootArgumentEntry.liveFrame root.frame id.val (root.valid id) := rfl

end DuplicatePrefix.AddFrameData
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.AddFrameData.raw, ``DuplicatePrefix.AddFrameData.cache,
      ``DuplicatePrefix.AddFrameData.write, ``DuplicatePrefix.AddFrameData.live_eq] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved root frame data dependency {dependency}"
