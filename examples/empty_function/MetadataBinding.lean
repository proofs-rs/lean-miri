import empty_function.Specification
import empty_function.MetadataQueries

/-! Immutable compiler facts bind static leaves; live ABI/instance demands bind
the selected World and retain their actual resulting machine state. -/
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

/-- Exact current-World cache evidence, rather than a saved Prepared ABI row. -/
theorem instance_abi (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (before : State) (world : SourceCompilerWorld.World) (abiId : Nat)
    (present : EvalCoreMachine.sourceCompilerAccess.get before = some world)
    (cached : SourceCompilerWorld.existingInstanceAbi world s.functionInstance #[] = .ok (some abiId))
    (query : SourceCompilerWorld.instanceAbi world s.functionInstance #[] = .ok s.abi) :
    (ExecutionMachine.callHooks s.cfg s.limits).fnAbiOfInstance () s.functionInstance #[] before = .ok s.abi before :=
  MetadataQueries.instance_abi (fields s metadata capacity) s.limits s.functionInstance s.abi
    before world abiId present cached query

/-- A newly derived ABI transports the real canonical-pool/memo delta. -/
theorem instance_abi_derived (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (before : State) (world derived installed : SourceCompilerWorld.World) (raw : Input.FunctionAbi) (abiId : Nat)
    (present : EvalCoreMachine.sourceCompilerAccess.get before = some world)
    (missing : SourceCompilerWorld.existingInstanceAbi world s.functionInstance #[] = .ok none)
    (derive : SourceAbi.derive world s.functionInstance #[] = .ok (derived,raw))
    (attach : SourceCompilerWorld.attachInstanceAbi derived s.functionInstance #[] raw = .ok (installed,abiId))
    (query : SourceCompilerWorld.instanceAbi installed s.functionInstance #[] = .ok s.abi) :
    (ExecutionMachine.callHooks s.cfg s.limits).fnAbiOfInstance () s.functionInstance #[] before =
      .ok s.abi (EvalCoreMachine.sourceCompilerAccess.put before installed) :=
  MetadataQueries.instance_abi_derived (fields s metadata capacity) s.limits s.functionInstance s.abi
    before world derived installed raw abiId present missing derive attach query

theorem target_features (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity) :
    (ExecutionMachine.callHooks s.cfg s.limits).checkTargetFeatures () s.functionInstance = pure () :=
  MetadataQueries.target_features (fields s metadata capacity) s.limits s.functionInstance metadata.targetFeatures

theorem not_closure (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (before : State) (world : SourceCompilerWorld.World) (node : Input.InstanceNode)
    (present : EvalCoreMachine.sourceCompilerAccess.get before = some world)
    (lookup : SourceCompilerWorld.node world s.functionInstance = .ok node)
    (kind : node.instanceKind = .Item metadata.itemDefinition) :
    (ExecutionMachine.callHooks s.cfg s.limits).nonCapturingClosure () s.functionInstance s.abi before = .ok false before :=
  MetadataQueries.not_closure (fields s metadata capacity) s.limits s.functionInstance metadata.itemDefinition s.abi
    before world node present lookup kind metadata.notClosure


end EmptyFunction.MetadataBinding

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.MetadataBinding." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved metadata binding axiom {dependency} in {name}"
