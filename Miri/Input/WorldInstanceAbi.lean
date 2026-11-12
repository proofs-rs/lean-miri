import Miri.Input.InstanceSignature
import Miri.Input.RawFunctionSignature
import Miri.ABI.FnAbi
import Miri.ABI.SignatureSeeds

/-! Source FnAbi construction for ordinary Item instances. The current target
classifier covers x86_64 Rust scalar, thin raw pointer, FnPtr and zero-sized
arguments. Other target, reference/aggregate, higher-ranked and caller-location cases retain explicit
capability errors. No imported ABI row supplies a constructed instance answer.
The rules are pinned rustc_ty_utils/src/abi.rs::fn_abi_new_uncached,
arg_attrs_for_rust_scalar and rustc_target::callconv::adjust_for_rust_abi. -/
namespace Miri.Input.WorldInstanceAbi
open Miri.ABI GenericSubstitution

private def liftPure (result : Except String α) : RuntimeArrayTypes.CompilerM α :=
  match result with | .ok value => pure value | .error error => throw error

private def classify (runtime : RuntimeMetadata) (id : TypeId) :
    RuntimeArrayTypes.CompilerM (ArgAbi TypeId) := do
  let layout ← RuntimeArrayTypes.liftType (RuntimeMetadata.layoutInWorld runtime id)
  if layout.layout.isZst then return ArgAbi.initial layout
  let arena := (← get).arena
  let constructor ← liftPure do
    match ← arena.lookupType id with
    | .constructed constructor => pure (some constructor)
    | .material source => arena.materialKey source
  if constructor.any (fun constructor => match constructor with
      | .rawPointer .. | .functionPointer .. => true | _ => false) then
    return ← liftPure (ArgAbi.conservativePointerScalar layout)
  liftPure (ArgAbi.nonPointerScalar layout 0)

/-- A source signature is instantiated and normalized in the execution World;
all appended type identities survive the ABI query. -/
def construct (instanceId : InstanceId) (extra : Array TypeId) :
    RuntimeArrayTypes.CompilerM (FnAbi TypeId) := do
  let world ← get
  unless world.metadata.source.producer.targetTriple.startsWith "x86_64-" &&
      world.metadata.target.pointerSize.bytes == 8 do
    throw "raw instance ABI classifier requires an x86_64 target"
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
  let args ← planned.inputs.mapM (classify world.metadata)
  let ret ← classify world.metadata planned.output
  let unwind : UnwindSeed := ⟨signature.abi,
    some ⟨policy.neverUnwind,policy.foreignItem,policy.dropGlue⟩,
    policy.panicUnwinds,policy.panicInDropUnwinds⟩
  pure ⟨args,ret,planned.cVariadic,UInt32.ofNat planned.fixedCount,conv,unwind.canUnwind⟩

end Miri.Input.WorldInstanceAbi
