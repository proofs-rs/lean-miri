import empty_function.Configuration
import empty_function.ScopedSafety

/-! An explicit, unfinished whole-call target and conditional assembly rule.
The domain/profile/metadata/resource/preservation predicates are parameters:
their complete data-only definitions and coverage remain open. In particular,
this file does not certify an arbitrary predicate as Rust input validity.
Stage-success hypotheses occur only in `conditionalComposition`; they are
unproved implementation obligations, never caller input assumptions. -/
namespace EmptyFunction.WholeCall
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option autoImplicit false

abbrev State := MachineHooks.State MiriMemoryKind Configuration.RootUser
abbrev Config := ExecutionMachine.Config MiriMemoryKind Configuration.RootUser Unit Unit ABI.ExternAbi Unit

structure Static where
  prepared : Input.EvalPreparation.Prepared
  bytes : Input.CompilerGlobalBytes.Prepared
  options : Input.EvalConfigurationCore.Options
  capacity : Nat
  cfg : Config
  built : Configuration.rootConfig prepared bytes options () capacity = .ok cfg
  limits : ExecutionMachine.Limits
  functionInstance : CallInstance
  loaded : LoadedBody
  abi : FnAbi TyId

structure Packet where
  before : State
  destination : RuntimeStackPlace Provenance
  returnBlock : BasicBlockId
  unwind : UnwindAction

def install (s : Static) (p : Packet) :=
  Call.initStackFrame (ExecutionMachine.callHooks s.cfg s.limits) ()
    s.functionInstance s.loaded s.abi #[] false p.destination
    (.goto (some p.returnBlock) p.unwind) p.before

def depth (p : Packet) : Nat := p.before.stack.frames.size + 1

/-- Successful actual machine steps within empty_function; the exit boundary prevents
execution of the caller's continuation from entering the function claim. -/
inductive Executes (s : Static) (entryDepth : Nat) : State → State → Prop where
  | refl (state) : Executes s entryDepth state state
  | next {start middle finish} :
      entryDepth ≤ start.stack.frames.size →
      ExecutionMachine.step s.cfg s.limits () start = (middle, .ok true) →
      Executes s entryDepth middle finish → Executes s entryDepth start finish

def Returned (p : Packet) (after : State) : Prop :=
  after.stack.frames.size = p.before.stack.frames.size ∧
  after.stack.frames.pop = p.before.stack.frames.pop ∧
  ∃ original caller,
    p.before.stack.currentFrame? = some original ∧ after.stack.currentFrame? = some caller ∧
    caller.body = original.body ∧ caller.bodyIdentity = original.bodyIdentity ∧
    caller.functionInstance = original.functionInstance ∧
    caller.localsIdentity = original.localsIdentity ∧
    caller.location = .mir ⟨p.returnBlock, 0⟩

def Result (s : Static) (preserves : Packet → State → Prop) (p : Packet) : Prop :=
  ∃ installed after,
    install s p = .ok () installed ∧
    installed.stack.frames.size = depth p ∧
    Executes s (depth p) installed after ∧
    Returned p after ∧ preserves p after ∧
    ScopedSafety.NoErrors s.cfg s.limits (fun _ _ => True) (depth p) installed ∧
    ScopedSafety.NoUB s.cfg s.limits (fun _ _ => True) (depth p) installed

/-- Parameterized goal, not a completed ordinary-input theorem. All five
predicates must be independently defined and reviewed before adoption. -/
def Target (s : Static) (metadata profile : Prop)
    (resourceMargins validInput : Packet → Prop)
    (preserves : Packet → State → Prop) : Prop :=
  metadata → profile → ∀ p, resourceMargins p → validInput p → Result s preserves p

/-- The missing stages are explicit theorem parameters. This logical assembly
rule does not prove their hypotheses or discharge input-domain coverage. -/
theorem conditionalComposition (s : Static) (metadata profile : Prop)
    (resourceMargins validInput : Packet → Prop) (preserves : Packet → State → Prop)
    (initialization : metadata → profile → ∀ p, resourceMargins p → validInput p →
      ∃ installed, install s p = .ok () installed ∧ installed.stack.frames.size = depth p)
    (bodyReturn : metadata → profile → ∀ p, resourceMargins p → validInput p →
      ∀ installed, install s p = .ok () installed →
      ∃ after, Executes s (depth p) installed after ∧ Returned p after ∧ preserves p after)
    (allPrefixes : metadata → profile → ∀ p, resourceMargins p → validInput p →
      ∀ installed, install s p = .ok () installed →
      ScopedSafety.NoErrors s.cfg s.limits (fun _ _ => True) (depth p) installed) :
    Target s metadata profile resourceMargins validInput preserves := by
  intro m model p resources valid
  obtain ⟨installed, initial, installedDepth⟩ := initialization m model p resources valid
  obtain ⟨after, execution, returned, saved⟩ := bodyReturn m model p resources valid installed initial
  have noErrors := allPrefixes m model p resources valid installed initial
  exact ⟨installed, after, initial, installedDepth, execution, returned, saved,
    noErrors, ScopedSafety.noUB_of_noErrors noErrors⟩

end EmptyFunction.WholeCall
