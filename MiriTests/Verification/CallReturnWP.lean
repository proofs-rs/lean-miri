import Miri.Verification.ExactWP
import MiriTests.ControlFlow.Transitions

namespace MiriTests.Verification.CallReturnWP

open Miri.MIR Miri.Interpreter Miri.Verification.StepWP Std.WP

set_option experimental.vcgen true

private def callKind : TerminatorKind :=
  .Call ControlTests.discr #[] ⟨0, #[]⟩ (some 1) .Continue .Normal ⟨0⟩

private def callee : Frame Unit Unit Unit :=
  ControlTests.prep ControlTests.fixture (.goto (some 1) .Continue)

private def terminators : ControlTests.H := { ControlTests.hooks with
  call := fun _ _ state =>
    match state.stack.pushFrame callee with
    | .ok stack => (ControlTests.log 10 { state with stack }, .ok ())
    | .error error => (state, .error (.stack error)) }

private def hooks := { ControlTests.stepHooks with
  terminator := fun choice term => ControlFlow.evalTerminator terminators choice term }

private def caller : Frame Unit Unit Unit := { ControlTests.fixture with
  body := { ControlTests.fixture.body with
    basicBlocks := #[ControlTests.block #[] callKind, ControlTests.block #[] .Return] } }

private def entry : ControlTests.S := ⟨⟨#[caller]⟩, []⟩

private abbrev DriverProgram := Program hooks (fun _ _ => True)
private def invoke : DriverProgram :=
  .instruction (.terminator (.Call ControlTests.discr #[] ⟨0, #[]⟩ (some 1) .Continue .Normal ⟨0⟩))
private def ret : DriverProgram := .instruction .ret
private def afterCall : ControlTests.S := ⟨⟨#[caller, callee]⟩, [9, 10]⟩
private def afterReturn : ControlTests.S :=
  ⟨⟨#[{ caller with location := .mir ⟨1, 0⟩ }]⟩, [9, 10, 9, 1, 2, 3, 4]⟩

private theorem returnToCaller (post : Unit → ControlTests.S → Prop) (completed : post () afterReturn) :
    Triple ret (· = afterCall) post (fun _ _ => False) := by
  vcgen [ret]
  subst_vars
  refine ⟨_, rfl, rfl, ⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  exact ⟨rfl, completed⟩

/-- The call callback pushes a frame in this fixture. The actual driver and
return transition resume the caller, and the client chooses its final post. -/
theorem callReturn (post : Unit → ControlTests.S → Prop) (completed : post () afterReturn) :
    Triple (Program.seq invoke ret) (· = entry) post (fun _ _ => False) := by
  vcgen [invoke, ret]
  subst_vars
  refine ⟨_, rfl, rfl, ⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  change true = true ∧ wp ret post (fun _ _ => False) afterCall
  exact ⟨rfl, Triple.iff.mp (returnToCaller post completed) afterCall rfl⟩

/-- The canonical machine selects its production rule with arbitrary success
and error continuations. -/
example {K U C O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (allowed : MachineHooks.State K U → C → Prop)
    (post : Bool → MachineHooks.State K U → Prop) (onError : StepError → MachineHooks.State K U → Prop) :
    Triple (OutcomeStep.step (hooks := ExecutionMachine.stepHooks config limits) (allowed := allowed))
      (Miri.Verification.CanonicalStepWP.outcomePre config limits allowed post onError) post onError := by
  vcgen <;> assumption

open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Verification in
/-- A Return stops on the protector-release error before copying or removing
the frame. The failed status is reported after writing back the tree. -/
theorem canonicalReturnProtectorFailure {K U O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U Unit O X Host) (limits : ExecutionMachine.Limits)
    (before : MachineHooks.State K U) (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (loc : Location) (block : BasicBlock) (value : OpTy Provenance)
    (tracker : MachineHooks.BorrowState) (owned : FrameState)
    (id : AllocId) (tag : BorTag) (info : AllocationInfo)
    (entry : LocalAllocation Provenance BorrowTree K) (updated : MemoryState Provenance BorrowTree K)
    (post : Bool → MachineHooks.State K U → Prop)
    (onError : StepError → MachineHooks.State K U → Prop)
    (current : before.stack.currentFrame? = some frame)
    (pc : frame.location = .mir loc) (selected : frame.body.basicBlocks[loc.block]? = some block)
    (slot : block.statements[loc.statementIndex]? = none) (opcode : block.terminator.kind = .Return)
    (notCleanup : block.cleanup = false)
    (prepared : let checked := ExecutionMachine.withValidation config limits
      TerminatorMachine.beforeTerminatorWithChoice checked.terminators (checked.preemptionChoice ()) before =
        .ok () before)
    (read : (ExecutionMachine.terminatorHooks config limits).returnOperand () before = (before, .ok value))
    (enabled : before.machine.borrowTracker = some tracker)
    (ownedFrame : frame.extra.borrowTracker = some owned) (ownedTags : owned.protectedTags = #[(id, tag)])
    (liveInfo : before.machine.memory.getAllocInfo id = .ok info) (liveKind : info.kind = .liveData)
    (ensured : let checked := ExecutionMachine.withValidation config limits
      (TypedMachineBindings.retagHooks checked.access checked.retag).ensureTreeExtra id before = .ok () before)
    (located : before.machine.memory.live.find? (fun entry => entry.1 == id) = some (id, entry))
    (missing : entry.allocation.extra.indexOfTag tag = none)
    (writeback : before.machine.memory.setLiveAllocation id
      (entry.allocation.setExtra entry.allocation.extra) = .ok updated)
    (classified : onError
      (.invalidProgram s!"protector release invariant: {reprStr (BorrowTree.ProtectorReleaseStatus.MissingTag tag)}")
      { before with machine := { before.machine with memory := updated } }) :
    Triple (OutcomeStep.step (hooks := ExecutionMachine.stepHooks config limits) (allowed := fun _ _ => True))
      (· = before) post onError := by
  vcgen
  rename_i state atEntry
  subst state
  intro choice _
  cases choice
  have returned : CanonicalStepWP.returnPre config limits () false (post true) onError before := by
    simp only [CanonicalStepWP.returnPre, InstructionWP.returnPreWithEffects, current, pc,
      selected, notCleanup, show (false != false) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    change InstructionWP.resultPre _ onError
      ((ExecutionMachine.terminatorHooks config limits).returnOperand () before)
    rw [read]
    dsimp only at ensured
    simp only [InstructionWP.resultPre, ProtectorReleaseWP.popRawPre, ProtectorReleaseWP.beforeStackPopPre,
      enabled, current, Option.isSome_some, ↓reduceIte,
      ownedFrame, ownedTags, ProtectorReleaseWP.stackEntriesPre, ProtectorReleaseWP.stackEntryPre,
      liveInfo, liveKind, beq_self_eq_true, RvalueWP.actionPre, ensured, located,
      ProtectorReleaseWP.releasePre, missing, writeback]
    simpa only [enabled, reprStr] using classified
  simp only [CanonicalStepWP.choicePre, driverChoicePreWith, current, pc, selected, slot,
    CanonicalStepWP.terminatorPre, ← RvalueWP.actionPre_eq_wp, RvalueWP.actionPre, prepared,
    CanonicalStepWP.selectedTerminatorPre, opcode, InstructionWP.terminatorPreWithReturn]
  exact returned

end MiriTests.Verification.CallReturnWP
