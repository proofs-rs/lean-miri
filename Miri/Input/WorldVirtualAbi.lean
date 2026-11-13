import Miri.Input.InstanceSignature
import Miri.Input.WorldFunctionPointerAbi

/-! Pinned rustc_ty_utils/abi.rs::make_thin_self_ptr and for_instance. Virtual
receiver lowering retains the source pointer/reference type and replaces only
its physical layout with *mut (). This is not a VTable shim signature. -/
namespace Miri.Input.WorldVirtualAbi
open Miri.ABI GenericSubstitution
private def liftPure (result : Except String α) : RuntimeArrayTypes.CompilerM α :=
  match result with | .ok value => pure value | .error error => throw error
private def constructor (id : TypeId) : RuntimeArrayTypes.CompilerM TypeArena.Constructor := do
  let arena := (← get).arena
  match ← liftPure (arena.lookupType id) with
  | .constructed value => pure value
  | .material source =>
    let some value ← liftPure (arena.materialKey source)
      | throw "Virtual receiver source constructor absent"
    pure value

/-- Immediate built-in pointer receivers to dyn. Newtype/Box receiver unwrapping
and by-value unsized self remain separate capabilities. Pointee size=0/align=1
is the pinned dynamic-layout constructor, not imported pointee information. -/
def receiver (session : AbiSessionMaterial) (id : TypeId) :
    RuntimeArrayTypes.CompilerM (ArgAbi TypeId) := do
  let source ← constructor id
  let (pointee,borrowed) ← match source with
    | .rawPointer child _ => pure (child,none)
    | .reference child mutability _ => pure (child,some mutability)
    | _ => throw "Virtual ABI receiver requires an immediate pointer/reference"
  unless (match ← constructor pointee with | .dynamic _ => true | _ => false) do
    throw "Virtual ABI receiver requires a dynamic pointee"
  let world ← get
  let thin ← liftPure (PrimitiveLayout.pointer world.metadata.target false none)
  let layout : TyAndLayout TypeId := ⟨id,thin⟩
  let mut regular : UInt16 := 128
  if let some mutability := borrowed then
    let permitted ← if session.optimization == .no then pure false
      else if mutability == .Not then WorldSourceAutoTraits.query pointee "freeze"
      else do
        if !(← WorldSourceAutoTraits.query pointee "unpin") then pure false
        else WorldSourceAutoTraits.query pointee "unsafe_unpin"
    if permitted then
      regular := regular ||| 8 ||| 512
      if mutability == .Not then regular := regular ||| 32 ||| 4
    -- llvmWritable applies only to Item instances, never Virtual.
  pure ⟨layout,.Direct {ArgAttributes.new with regular}⟩

def construct (instanceId : InstanceId) (extra : Array TypeId) :
    RuntimeArrayTypes.CompilerM (FnAbi TypeId) := do
  let world ← get
  unless world.metadata.source.producer.targetTriple.startsWith "x86_64-" &&
      world.metadata.target.defaultAddressSpace == .ZERO && world.metadata.target.pointerSize.bytes == 8 do
    throw "Virtual ABI requires an x86_64 data-pointer target"
  let some session := world.metadata.source.producer.abiSession
    | throw "Virtual ABI canonical session configuration absent"
  let key ← liftPure do
    match ← world.instances.lookup instanceId with | .material key | .constructed key => pure key
  let .Virtual definition _ := key.kind | throw "Virtual ABI requires a Virtual key"
  let some source := world.metadata.source.definitions[definition]?
    | throw "Virtual ABI source declaration absent"
  let some callable := source.callableSource | throw "Virtual ABI callable source header absent"
  unless callable.hasSelf && callable.definitionKind == "associated_function" && callable.container == some "trait" do
    throw "Virtual ABI requires an associated trait method"
  let some trackCaller := source.bodyTrackCaller
    | throw "Virtual ABI caller-location attribute absent"
  if trackCaller then throw "Virtual ABI caller-location argument construction unavailable"
  let raw ← InstanceSignature.instantiate 16384 instanceId
  let signature ← liftPure (WorldFunctionPointerAbi.erasedSourceSignature raw)
  unless !signature.cVariadic && extra.isEmpty do throw "Virtual ABI variadic extras unavailable"
  let conv ← match signature.abi with
    | .Rust | .RustCall => pure CanonAbi.Rust
    | .RustCold => pure .RustCold
    | .RustPreserveNone => pure .RustPreserveNone
    | .RustTail => pure .RustTail
    | _ => throw "Virtual ABI foreign calling convention unavailable"
  let resolve (term : Term) := RuntimeArrayTypes.liftType
    (WorldNormalization.resolveNormalizedTerm world.metadata.normalizationContext 100000 16384 term)
  let inputs ← signature.inputs.mapM resolve
  let output ← resolve signature.output
  let world ← get
  let tupleFields (id : TypeId) := match world.arena.lookupType id with
    | .ok (.constructed (.tuple fields)) => some fields
    | .ok (.material source) => match source.shape with | .tuple fields => some fields | _ => none
    | _ => none
  let plan ← liftPure ((SignatureSeed.mk inputs output signature.abi signature.cVariadic).plan extra none tupleFields)
  unless plan.fixedCount < 2^32 do throw "Virtual ABI fixed count exceeds u32"
  let some selfType := plan.inputs[0]? | throw "Virtual ABI receiver absent"
  let self ← receiver session selfType
  let tail ← plan.inputs.extract 1 plan.inputs.size |>.mapM (WorldAbiScalar.classify world.metadata session none false)
  let args := #[self] ++ tail
  let ret ← WorldAbiScalar.classify world.metadata session none true plan.output
  if (args.push ret).any (fun arg => match arg.mode with | .Indirect .. => true | _ => false) then
    throw "Virtual ABI indirect argument/return adjustment unavailable"
  -- Virtual ignores trait-method rustc_nounwind, has no Item MIR deductions,
  -- and retains the exact ABI/session panic policy (abi.rs:610).
  let unwind : UnwindSeed := ⟨signature.abi,none,session.panic == .unwind,session.panicInDrop == .unwind⟩
  pure ⟨args,ret,plan.cVariadic,UInt32.ofNat plan.fixedCount,conv,unwind.canUnwind⟩
end Miri.Input.WorldVirtualAbi
