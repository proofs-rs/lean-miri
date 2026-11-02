import empty_function.LocalIndirectPreflight
namespace EmptyFunction.LocalIndirectCore
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.Configuration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
def rawCore (s : Static) (destination : RuntimeStackPlace Provenance) (place : MPlaceTy Provenance) (continuation : ReturnContinuation) :
    MachineHooks.M MiriMemoryKind Configuration.RootUser Unit := do
  let hooks := ExecutionMachine.callHooks s.cfg s.limits
  hooks.pushRaw () s.functionInstance s.loaded destination (CanonicalInit.normalizedContinuation s continuation)
  let frame ← MachineHooks.currentFrame
  let preamble ← match frame.location with
    | .unwinding span => pure span
    | .mir _ => throw (StepError.invalidProgram "raw frame does not have preamble location")
  MachineHooks.setCurrentFrame {frame with trackCallerArg := none}
  CanonicalInit.spanAt (← hooks.localSpan s.loaded.body 0)
  hooks.protectArgument () place
  CanonicalInit.spanAt preamble
  hooks.pushDone ()
 theorem core_reduction (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (destination : RuntimeStackPlace Provenance) (place : MPlaceTy Provenance) (continuation : ReturnContinuation) :
    Call.zeroIndirectCore (ExecutionMachine.callHooks s.cfg s.limits) () s.functionInstance s.loaded s.abi
      destination place continuation = rawCore s destination place continuation := by
  let hooks := ExecutionMachine.callHooks s.cfg s.limits
  have mode : hooks.withRetagMode () .FnEntry (pure ((0,0) : Nat × Nat)) = pure (0,0) := by
    funext state
    exact Init.mode_pure .FnEntry ((0,0) : Nat × Nat) state
  have compatible : hooks.checkArgumentCompat () s.abi.ret s.abi.ret = pure true :=
    CanonicalInit.return_compatibility s metadata capacity
  have after : hooks.afterFrameInit () = pure () := rfl
  change Call.zeroIndirectCore hooks () s.functionInstance s.loaded s.abi destination place continuation = _
  unfold Call.zeroIndirectCore rawCore
  simp only [mode,compatible,after,bind_pure_comp,bind_assoc,pure_bind]
  with_unfolding_all rfl


theorem entry_core (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (destination : RuntimeStackPlace Provenance) (place : MPlaceTy Provenance) (continuation : ReturnContinuation)
    (before cached : State)
    (preflight : (ExecutionMachine.callHooks s.cfg s.limits).placeToOp () destination before =
      .ok ⟨.indirect place.mplace,place.layout⟩ cached) :
    Call.initStackFrame (ExecutionMachine.callHooks s.cfg s.limits) () s.functionInstance
      s.loaded s.abi #[] false destination continuation before =
      rawCore s destination place continuation cached := by
  let hooks := ExecutionMachine.callHooks s.cfg s.limits
  have variadic : hooks.abiVariadic s.abi = false := metadata.notVariadic
  have convention : hooks.sameConvention s.abi s.abi = true := by
    change (s.abi.conv == s.abi.conv) = true
    exact beq_self_eq_true _
  have arguments : hooks.abiArgs s.abi = #[] := metadata.noArguments
  have ret : hooks.abiReturn s.abi = s.abi.ret := rfl
  have count : s.loaded.body.argumentCount = 0 := by rw [metadata.body]; exact Program.no_arguments
  rw [Call.zero_entry_indirect hooks () s.functionInstance s.loaded s.abi destination continuation before cached place
    (MetadataBinding.caller_location s metadata capacity) (MetadataBinding.instance_abi s metadata capacity)
    (MetadataBinding.target_features s metadata capacity) preflight (MetadataBinding.not_closure s metadata capacity)
    variadic convention arguments ret count]
  rw [core_reduction s metadata capacity]

end EmptyFunction.LocalIndirectCore
