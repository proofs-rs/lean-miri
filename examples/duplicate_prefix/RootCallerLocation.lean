import duplicate_prefix.HelperCompilerFacts
import duplicate_prefix.CallEntryLocals
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.RootCallerLocation
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
 theorem scope0 : CompilerScopes.sourceScope PreparedReflection.actual.compiler.lifecycle.calls.scopes 1 0 =
    .ok ⟨none,none⟩ := by with_unfolding_all rfl
 theorem scope1 : CompilerScopes.sourceScope PreparedReflection.actual.compiler.lifecycle.calls.scopes 1 1 =
    .ok ⟨none,none⟩ := by with_unfolding_all rfl
 theorem source_scope0 (state : CanonicalConfigFacts.RootState) :
    (CompilerVirtualLeaves.make (C := Unit) PreparedReflection.actual.compiler.lifecycle.calls).sourceScope
      RootBody.reflected.body.identity RootBody.reflected.functionInstance RootBody.reflected.body.body 0 state =
      .ok ⟨none,none⟩ state := by
  with_unfolding_all change
    (do
      unless RootBody.reflected.body.body == RootBody.reflected.body.body do
        throw (.invalidProgram "frame body identity/content mismatch")
      pure (⟨none,none⟩ : VirtualCalls.CallerScope) : MachineHooks.M MiriMemoryKind Machine.RootUser _) state = _
  simp only [beq_self_eq_true, Bool.not_true, ite_false, ite_true, pure_bind, pure, EStateM.pure]
 theorem source_scope1 (state : CanonicalConfigFacts.RootState) :
    (CompilerVirtualLeaves.make (C := Unit) PreparedReflection.actual.compiler.lifecycle.calls).sourceScope
      RootBody.reflected.body.identity RootBody.reflected.functionInstance RootBody.reflected.body.body 1 state =
      .ok ⟨none,none⟩ state := by
  with_unfolding_all change
    (do
      unless RootBody.reflected.body.body == RootBody.reflected.body.body do
        throw (.invalidProgram "frame body identity/content mismatch")
      pure (⟨none,none⟩ : VirtualCalls.CallerScope) : MachineHooks.M MiriMemoryKind Machine.RootUser _) state = _
  simp only [beq_self_eq_true, Bool.not_true, ite_false, ite_true, pure_bind, pure, EStateM.pure]
noncomputable def sourceInfo (blockId : Nat) : MIR.SourceInfo :=
  match RootBody.reflected.body.body.basicBlocks[blockId]? with
  | none => ⟨⟨0⟩,0⟩
  | some block => match block.terminator.kind with
    | TerminatorKind.Call _ _ _ _ _ _ functionSpan => {block.terminator.sourceInfo with span := functionSpan}
    | _ => block.terminator.sourceInfo
 theorem add_scope : (sourceInfo 7).scope = 1 := by with_unfolding_all rfl
 theorem copy_scope : (sourceInfo 8).scope = 1 := by with_unfolding_all rfl
 theorem span_at_scope1 (budget : Nat) (info : MIR.SourceInfo) (scope : info.scope = 1)
    (state : CanonicalConfigFacts.RootState) :
    VirtualCalls.callerLocationSpan (CompilerVirtualLeaves.make (C := Unit) PreparedReflection.actual.compiler.lifecycle.calls)
      RootBody.reflected.body.identity RootBody.reflected.functionInstance RootBody.reflected.body.body none
      (budget+1) info state = .ok info.span state := by
  unfold VirtualCalls.callerLocationSpan
  simp only [scope, bind, EStateM.bind]
  rw [source_scope1]
  rfl
noncomputable def statementCount (blockId : Nat) : Nat :=
  ((RootBody.reflected.body.body.basicBlocks[blockId]?).map (·.statements.size)).getD 0
 theorem caller_at_add
    (leaves : ExecutionCallLeaves.Virtual MiriMemoryKind Machine.RootUser Unit)
    (compiler : leaves.compiler = CompilerVirtualLeaves.make PreparedReflection.actual.compiler.lifecycle.calls)
    (access : PlaceMachine.AccessConfig MiriMemoryKind Machine.RootUser)
    (operands : OperandMachine.Hooks MiriMemoryKind Machine.RootUser Unit) (debug : Bool)
    (budget : Nat) (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (tracked : frame.trackCallerArg = none)
    (location : frame.location = .mir ⟨7,statementCount 7⟩) :
    VirtualCalls.callerLocation (ExecutionCalls.virtualHooks leaves access operands debug) (budget+1)
      (Storage.withCurrent frames frame machine) =
      .ok (sourceInfo 7).span (Storage.withCurrent frames frame machine) := by
  unfold VirtualCalls.callerLocation
  simp only [ExecutionCalls.virtualHooks, MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?,
    Array.back?_push, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  rw [location, body]
  with_unfolding_all change (VirtualCalls.callerLocationSpan leaves.compiler frame.bodyIdentity frame.functionInstance
    RootBody.reflected.body.body frame.trackCallerArg (budget+1) (sourceInfo 7) _ = _)
  rw [compiler, identity, callee, tracked]
  exact span_at_scope1 budget (sourceInfo 7) add_scope _
 theorem caller_at_copy
    (leaves : ExecutionCallLeaves.Virtual MiriMemoryKind Machine.RootUser Unit)
    (compiler : leaves.compiler = CompilerVirtualLeaves.make PreparedReflection.actual.compiler.lifecycle.calls)
    (access : PlaceMachine.AccessConfig MiriMemoryKind Machine.RootUser)
    (operands : OperandMachine.Hooks MiriMemoryKind Machine.RootUser Unit) (debug : Bool)
    (budget : Nat) (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (tracked : frame.trackCallerArg = none)
    (location : frame.location = .mir ⟨8,statementCount 8⟩) :
    VirtualCalls.callerLocation (ExecutionCalls.virtualHooks leaves access operands debug) (budget+1)
      (Storage.withCurrent frames frame machine) =
      .ok (sourceInfo 8).span (Storage.withCurrent frames frame machine) := by
  unfold VirtualCalls.callerLocation
  simp only [ExecutionCalls.virtualHooks, MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?,
    Array.back?_push, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  rw [location, body]
  with_unfolding_all change (VirtualCalls.callerLocationSpan leaves.compiler frame.bodyIdentity frame.functionInstance
    RootBody.reflected.body.body frame.trackCallerArg (budget+1) (sourceInfo 8) _ = _)
  rw [compiler, identity, callee, tracked]
  exact span_at_scope1 budget (sourceInfo 8) copy_scope _
 theorem actual_caller_at_add
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (budget : Nat) (positive : limits.callDispatch = budget+1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (tracked : frame.trackCallerArg = none)
    (location : frame.location = .mir ⟨7,statementCount 7⟩) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).callerLocation
      (Storage.withCurrent frames frame machine) =
      .ok (sourceInfo 7).span (Storage.withCurrent frames frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let bound := ExecutionMachine.withValidation config limits
  change VirtualCalls.callerLocation
    (ExecutionCalls.virtualHooks bound.virtual bound.access (ExecutionMachine.operandHooks bound) bound.compiler.debugAssertions)
    limits.callDispatch _ = _
  rw [positive]
  exact caller_at_add bound.virtual (CanonicalConfigFacts.actual_fields options () remaining span).virtualCompiler
    bound.access (ExecutionMachine.operandHooks bound) bound.compiler.debugAssertions budget frames frame machine
    body identity callee tracked location
 theorem actual_caller_at_copy
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (budget : Nat) (positive : limits.callDispatch = budget+1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (tracked : frame.trackCallerArg = none)
    (location : frame.location = .mir ⟨8,statementCount 8⟩) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).callerLocation
      (Storage.withCurrent frames frame machine) =
      .ok (sourceInfo 8).span (Storage.withCurrent frames frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let bound := ExecutionMachine.withValidation config limits
  change VirtualCalls.callerLocation
    (ExecutionCalls.virtualHooks bound.virtual bound.access (ExecutionMachine.operandHooks bound) bound.compiler.debugAssertions)
    limits.callDispatch _ = _
  rw [positive]
  exact caller_at_copy bound.virtual (CanonicalConfigFacts.actual_fields options () remaining span).virtualCompiler
    bound.access (ExecutionMachine.operandHooks bound) bound.compiler.debugAssertions budget frames frame machine
    body identity callee tracked location
end DuplicatePrefix.RootCallerLocation
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.RootCallerLocation." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved caller-location dependency {dependency}"
