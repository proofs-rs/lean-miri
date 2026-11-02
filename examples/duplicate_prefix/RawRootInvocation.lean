import duplicate_prefix.EmptyRootCallEntry
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.RawRootInvocation
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open RootFrameData
noncomputable def machine (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :=
  CallEntryFacts.cacheTop (CallEntryFacts.freshRoot before).1 frames.size
noncomputable def root (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) (race : before.dataRace = none) : RootFrame :=
  RootFrameData.raw (CallEntryFacts.freshRoot before).1 (.memory place) (CallEntryFacts.freshRoot before).2 race
 theorem raw_eq (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) (race : before.dataRace = none) :
    CallEntryFacts.rawPushedState frames before (.memory place) =
      Storage.withCurrent frames (root before place race).frame (machine frames before) := rfl
 theorem control (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) (race : before.dataRace = none) :
    (root before place race).frame.location = .unwinding ⟨559⟩ ∧
    (root before place race).frame.trackCallerArg = none ∧
    (root before place race).frame.returnContinuation = .stop true ∧
    (root before place race).frame.returnPlace = .memory place := ⟨rfl,rfl,rfl,rfl⟩
 theorem locals (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) (race : before.dataRace = none) :
    (root before place race).frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
  RootEntryFrame.raw_locals _ _ _
 theorem frame_borrow (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) (race : before.dataRace = none)
    (tracker : MachineHooks.BorrowState) (enabled : before.borrowTracker = some tracker) :
    (root before place race).frame.extra.borrowTracker = some {} :=
  RootEntryFrame.raw_borrow _ _ _ tracker enabled
 theorem preservation (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    (machine frames before).memory = before.memory ∧
    (machine frames before).borrowTracker = before.borrowTracker ∧
    (machine frames before).dataRace = before.dataRace ∧
    (machine frames before).user.addresses = before.user.addresses ∧
    (machine frames before).user.payload.ghost = before.user.payload.ghost ∧
    (machine frames before).user.payload.validation = before.user.payload.validation ∧
    (machine frames before).user.payload.payload.user.types = before.user.payload.payload.user.types ∧
    (machine frames before).user.payload.payload.user.backend = before.user.payload.payload.user.backend ∧
    (machine frames before).user.payload.payload.user.runtime.extras = before.user.payload.payload.user.runtime.extras := by
  constructor <;> try rfl
  all_goals repeat' constructor
  all_goals rfl
end DuplicatePrefix.RawRootInvocation
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.RawRootInvocation.raw_eq, ``DuplicatePrefix.RawRootInvocation.control,
      ``DuplicatePrefix.RawRootInvocation.locals, ``DuplicatePrefix.RawRootInvocation.frame_borrow,
      ``DuplicatePrefix.RawRootInvocation.preservation] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved raw root invocation dependency {dependency}"
