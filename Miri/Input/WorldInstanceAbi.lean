import Miri.Input.InstanceSignature
import Miri.Input.RawFunctionSignature
import Miri.ABI.FnAbi
import Miri.ABI.SignatureSeeds
import Miri.Input.WorldAbiScalar

/-! Source FnAbi construction for ordinary Item instances. The current target
classifier covers x86_64 Rust scalar, thin raw pointer, FnPtr, thin references
and zero-sized arguments. Other target, aggregate, higher-ranked and caller-location cases retain explicit
capability errors. No imported ABI row supplies a constructed instance answer.
The rules are pinned rustc_ty_utils/src/abi.rs::fn_abi_new_uncached,
arg_attrs_for_rust_scalar and rustc_target::callconv::adjust_for_rust_abi. -/
namespace Miri.Input.WorldInstanceAbi
open Miri.ABI GenericSubstitution

private def liftPure (result : Except String α) : RuntimeArrayTypes.CompilerM α :=
  match result with | .ok value => pure value | .error error => throw error

/-- A source signature is instantiated and normalized in the execution World;
all appended type identities survive the ABI query. -/
def construct (instanceId : InstanceId) (extra : Array TypeId) :
    RuntimeArrayTypes.CompilerM (FnAbi TypeId) := do
  let world ← get
  unless world.metadata.source.producer.targetTriple.startsWith "x86_64-" &&
      world.metadata.target.pointerSize.bytes == 8 do
    throw "raw instance ABI classifier requires an x86_64 target"
  let some session := world.metadata.source.producer.abiSession
    | throw "raw ABI session configuration is absent"
  let key ← liftPure do
    match ← world.instances.lookup instanceId with
    | .material key | .constructed key => pure key
  let .Item definition := key.kind | throw "raw instance ABI requires an ordinary Item"
  let some source := world.metadata.source.definitions[definition]?
    | throw "raw instance ABI definition is absent"
  let some policy := source.functionAbiMaterial
    | throw "raw instance ABI codegen and panic policy are absent"
  let some trackCaller := source.bodyTrackCaller
    | throw "raw instance ABI caller-location attribute is absent"
  if trackCaller then throw "raw instance ABI caller-location argument construction is unavailable"
  let raw ← InstanceSignature.instantiate 16384 instanceId
  let signature ← liftPure (RawFunctionSignature.read raw)
  unless signature.variables.isEmpty do
    throw "raw instance ABI higher-ranked signature normalization is unavailable"
  let conv ← match signature.abi with
    | .Rust | .RustCall => pure CanonAbi.Rust
    | .RustCold => pure .RustCold
    | .RustPreserveNone => pure .RustPreserveNone
    | .RustTail => pure .RustTail
    | _ => throw "raw instance ABI foreign calling-convention classification is unavailable"
  let resolve (term : Term) : RuntimeArrayTypes.CompilerM TypeId :=
    RuntimeArrayTypes.liftType (WorldNormalization.resolveNormalizedTerm
      world.metadata.normalizationContext 100000 16384 term)
  let inputs ← signature.inputs.mapM resolve
  let output ← resolve signature.output
  let world ← get
  for id in extra do let _ ← liftPure (world.arena.lookupType id); pure ()
  let tupleFields (id : Nat) :=
    match (world.arena.lookupType id).toOption with
    | some (.material node) => match node.shape with | .tuple fields => some fields | _ => none
    | some (.constructed (.tuple fields)) => some fields
    | _ => none
  let seed : SignatureSeed TypeId := ⟨inputs,output,signature.abi,signature.cVariadic⟩
  let planned ← liftPure (seed.plan extra none tupleFields)
  unless planned.fixedCount < 2^32 do throw "raw instance ABI fixed argument count exceeds u32"
  let args ← planned.inputs.mapM (WorldAbiScalar.classify world.metadata session (some policy) false)
  let ret ← WorldAbiScalar.classify world.metadata session (some policy) true planned.output
  let unwind : UnwindSeed := ⟨signature.abi,
    some ⟨policy.neverUnwind,policy.foreignItem,policy.dropGlue⟩,
    session.panic == .unwind,session.panicInDrop == .unwind⟩
  pure ⟨args,ret,planned.cVariadic,UInt32.ofNat planned.fixedCount,conv,unwind.canUnwind⟩

end Miri.Input.WorldInstanceAbi
