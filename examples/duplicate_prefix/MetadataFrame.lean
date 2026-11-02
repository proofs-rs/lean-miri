import duplicate_prefix.MetadataEntryFacts
namespace DuplicatePrefix.MetadataFrame
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
def rank (crates : Array Nat) : UInt8 :=
  if MetadataEntryFacts.definition.crateIndex == PreparedReflection.actual.compiler.lifecycle.frames.localCrate then 255
  else if crates.contains MetadataEntryFacts.definition.crateIndex then 255 else 1

def rawFrame (crates : Array Nat) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (destination : RuntimeStackPlace Provenance) (identity : LocalsIdentity) :
    Frame Provenance LocalLayout MachineHooks.FrameExtra :=
  let frame : Frame Provenance LocalLayout Unit := Frame.create PtrMetadataHelper.body
    PtrMetadataHelper.resolved.callee () (.goto (some 1) .Continue) destination MetadataEntryFacts.metadataPreamble identity
  { body := frame.body, bodyIdentity := frame.bodyIdentity, functionInstance := frame.functionInstance
    extra := {borrowTracker := machine.borrowTracker.map (fun _ => {}), catchUnwind := none, userRelevance := rank crates, dataRace := machine.dataRace.map (fun _ => {})}
    returnContinuation := frame.returnContinuation, returnPlace := frame.returnPlace
    localsIdentity := frame.localsIdentity, locals := frame.locals, vaList := frame.vaList
    trackCallerArg := frame.trackCallerArg, location := frame.location }

theorem init_frame (crates : Array Nat)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (destination : RuntimeStackPlace Provenance) (identity : LocalsIdentity) :
    MachineHooks.initFrame (FrameMetadata.userRelevance
      (CompilerFrameMetadata.hooks PreparedReflection.actual.compiler.lifecycle.frames crates))
      (Frame.create PtrMetadataHelper.body PtrMetadataHelper.resolved.callee ()
        (.goto (some 1) .Continue) destination MetadataEntryFacts.metadataPreamble identity) state =
      .ok (rawFrame crates state.machine destination identity) state := by
  unfold MachineHooks.initFrame
  have relevance := MetadataEntryFacts.user_relevance crates
    (Frame.create PtrMetadataHelper.body PtrMetadataHelper.resolved.callee ()
      (.goto (some 1) .Continue) destination MetadataEntryFacts.metadataPreamble identity : Frame Provenance LocalLayout Unit) state rfl
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    pure, EStateM.pure] at relevance ⊢
  rw [relevance]
  rfl
end
end DuplicatePrefix.MetadataFrame

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.MetadataFrame.init_frame) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved metadata frame dependency {dependency}"
