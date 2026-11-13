import Miri.Input.WorldAbiScalar
import Miri.Input.RawFunctionSignature
import Miri.ABI.SignatureSeeds
import Miri.Input.BinderRegions

namespace Miri.Input.WorldFunctionPointerAbi
open Miri.ABI GenericSubstitution
private def liftPure (result : Except String α) : RuntimeArrayTypes.CompilerM α :=
  match result with | .ok result => pure result | .error error => throw error

/-- Remove only this FnSig binder. Inner binders retain their own bound regions. -/
private def eraseSignatureBinder : Nat → Nat → Term → Except String Term
  | 0,_,_ => throw "function pointer binder erasure exhausted"
  | fuel+1,depth,term => do
    match term with
    | .bound .region (.Bound index) boundVariable identity =>
      if index == depth then pure (.atom .region "erased" "")
      else if index > depth then pure (.bound .region (.Bound (index-1)) boundVariable identity)
      else pure term
    | .binder variables body => pure (.binder variables (← eraseSignatureBinder fuel (depth+1) body))
    | .node sort tag payload children => pure (.node sort tag payload (← children.mapM (eraseSignatureBinder fuel depth)))
    | .definition sort tag identity children => pure (.definition sort tag identity (← children.mapM (eraseSignatureBinder fuel depth)))
    | _ => pure term

def sourceSignature (world : TypeArena.World) (id : TypeId) : Except String RawFunctionSignature.Signature := do
  let term ← GenericInstantiationWorld.ofType world 16384 id
  let .node .type "function_pointer" "" (.cons binder .nil) := term
    | throw "function pointer ABI requires its source FnPtr constructor"
  BinderRegions.validateClosed #[] 16384 binder
  let .binder variables body := binder | throw "function pointer signature binder absent"
  unless variables.all (fun boundVariable => match boundVariable with | .region _ => true | _ => false) do
    throw "function pointer signature contains non-region bound variables"
  let erased ← BinderRegions.eraseAndAnonymize 16384 (.binder #[] (← eraseSignatureBinder 16384 0 body))
  RawFunctionSignature.read erased

def construct (id : TypeId) (extra : Array TypeId) :
    RuntimeArrayTypes.CompilerM (FnAbi TypeId) := do
  let world ← get
  unless world.metadata.source.producer.targetTriple.startsWith "x86_64-" &&
      world.metadata.target.pointerSize.bytes == 8 do throw "function pointer ABI target unavailable"
  let some session := world.metadata.source.producer.abiSession
    | throw "raw ABI session configuration is absent"
  let signature ← liftPure (sourceSignature world.arena id)
  if signature.cVariadic then throw "function pointer ABI variadic classification is unavailable"
  let conv ← match signature.abi with
    | .Rust | .RustCall => pure CanonAbi.Rust
    | .RustCold => pure .RustCold
    | .RustPreserveNone => pure .RustPreserveNone
    | .RustTail => pure .RustTail
    | _ => throw "function pointer ABI calling convention unavailable"
  let resolve (term : Term) : RuntimeArrayTypes.CompilerM TypeId :=
    RuntimeArrayTypes.liftType (WorldNormalization.resolveNormalizedTerm
      world.metadata.normalizationContext 100000 16384 term)
  let inputs ← signature.inputs.mapM resolve
  let output ← resolve signature.output
  let world ← get
  let tupleFields (id : TypeId) := match world.arena.lookupType id with
    | .ok (.constructed (.tuple fields)) => some fields
    | .ok (.material source) => match source.shape with | .tuple fields => some fields | _ => none
    | _ => none
  let plan ← liftPure ((SignatureSeed.mk inputs output signature.abi signature.cVariadic).plan extra none tupleFields)
  unless plan.fixedCount < 2^32 do throw "function pointer ABI fixed count exceeds u32"
  let args ← plan.inputs.mapM (WorldAbiScalar.classify world.metadata session none false)
  let ret ← WorldAbiScalar.classify world.metadata session none true plan.output
  if conv == .RustTail && args.any (fun arg => match arg.mode with | .Indirect .. => true | _ => false) then
    throw "RustTail indirect argument stack adjustment is unavailable"
  let unwind : UnwindSeed := ⟨signature.abi,none,session.panic == .unwind,session.panicInDrop == .unwind⟩
  pure ⟨args,ret,plan.cVariadic,UInt32.ofNat plan.fixedCount,conv,unwind.canUnwind⟩
end Miri.Input.WorldFunctionPointerAbi
