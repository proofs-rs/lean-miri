import empty_function.Specification
import empty_function.MetadataQueries

/-! The pure metadata contract discharges actual canonical call-hook checks.
No stage-success witness is an input of these theorems. -/
namespace EmptyFunction.MetadataBinding
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter
open EmptyFunction.Specification EmptyFunction.WholeCall
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem fields (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity) :
    CanonicalDictionaries.Fields s.prepared.compiler (EmptyFunction.Configuration.proofOptions s.options) s.cfg := by
  obtain ⟨remaining, eq⟩ : ∃ n : Nat, s.capacity = n+1 := ⟨s.capacity-1, by omega⟩
  apply CanonicalDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options)
    (Configuration.leaves s.prepared s.options.place.debugAssertions) remaining metadata.construction s.cfg
  simpa only [Configuration.rootConfig, eq] using s.built

theorem caller_location (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity) :
    (ExecutionMachine.callHooks s.cfg s.limits).requiresCallerLocation s.functionInstance = pure false :=
  MetadataQueries.caller_location (fields s metadata capacity) s.limits s.functionInstance
    metadata.inlineAttribute metadata.trackCaller

theorem instance_abi (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity) :
    (ExecutionMachine.callHooks s.cfg s.limits).fnAbiOfInstance () s.functionInstance #[] = pure s.abi :=
  MetadataQueries.instance_abi (fields s metadata capacity) s.limits s.functionInstance s.abi metadata.abi

theorem target_features (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity) :
    (ExecutionMachine.callHooks s.cfg s.limits).checkTargetFeatures () s.functionInstance = pure () :=
  MetadataQueries.target_features (fields s metadata capacity) s.limits s.functionInstance metadata.targetFeatures

theorem not_closure (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity) :
    (ExecutionMachine.callHooks s.cfg s.limits).nonCapturingClosure () s.functionInstance s.abi = pure false := by
  exact MetadataQueries.not_closure (fields s metadata capacity) s.limits
    s.functionInstance metadata.itemDefinition s.abi metadata.itemKind metadata.notClosure

end EmptyFunction.MetadataBinding

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.MetadataBinding." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved metadata binding axiom {dependency} in {name}"
