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

/-- Bounded source subset of abi.rs::make_thin_self_ptr/non_1zst_field.
Exactly one raw declared field means no ignored 1-ZST search or copied projection.
Only repr(transparent) structs with no repr align/pack and at most two wrappers
are admitted. Other DispatchFromDyn newtypes remain explicit residuals. -/
private def unwrapRawReceiver : Nat → TypeId → RuntimeArrayTypes.CompilerM TypeId
  | 0, _ => throw "Virtual transparent receiver exceeds two source wrappers"
  | fuel + 1, id => do
    match ← constructor id with
    | .rawPointer child _ =>
      unless (match ← constructor child with | .dynamic _ => true | _ => false) do
        throw "Virtual transparent receiver raw pointee is not dyn"
      pure id
    | .adt .. =>
      let metadata := (← get).metadata
      let declaration ← RuntimeArrayTypes.liftType (RuntimeMetadata.adtDeclarationInWorld metadata id)
      unless declaration.kind == .structKind && declaration.representation.transparent &&
          declaration.representation.alignBytes.isNone && declaration.representation.packBytes.isNone &&
          declaration.variants.size == 1 && declaration.variants[0]?.any (·.fieldCount == 1) &&
          declaration.fields.size == 1 do
        throw "Virtual receiver requires a one-field transparent raw-pointer wrapper"
      -- No copied material parent geometry may justify raw-field unwrapping.
      let before := (← get).arena
      if let .material node ← liftPure (before.lookupType id) then
        unless metadata.source.layouts[node.layoutId]?.any (·.structType == some id) do
          throw "Virtual transparent receiver source struct layout provider unavailable"
      -- Every physical premise is recomputed from source declarations/field syntax.
      let parent ← RuntimeArrayTypes.liftType (RuntimeMetadata.layoutInWorld metadata id)
      unless parent.layout.isSized do throw "Virtual transparent receiver wrapper is unsized"
      unless (match parent.layout.backendRepr with | .Scalar .. | .ScalarPair .. => true | _ => false) do
        throw "Virtual transparent receiver lacks scalar/scalar-pair source layout"
      let field ← RuntimeArrayTypes.liftType (RuntimeMetadata.fieldTypeInWorld metadata id 0 0)
      let fieldWorld := (← get).arena
      if let .material node ← liftPure (fieldWorld.lookupType field) then
        let some seed := metadata.source.layouts[node.layoutId]?
          | throw "Virtual transparent receiver field source layout seed absent"
        unless seed.pointerType == some field || seed.structType == some field do
          throw "Virtual transparent receiver field source layout provider unavailable"
      let fieldLayout ← RuntimeArrayTypes.liftType (RuntimeMetadata.layoutInWorld metadata field)
      unless fieldLayout.layout.size.bytes != 0 || fieldLayout.layout.align.abi.pow2 != 0 do
        throw "Virtual transparent receiver field is a 1-ZST"
      unwrapRawReceiver fuel field
    | _ => throw "Virtual transparent receiver terminal is not a raw pointer"

/-- Disjoint source receiver policy: immediate builtin pointers, unsized dyn
by-value, or the bounded transparent raw-pointer family. Successful field/type
interning updates stay in the same CompilerM World; no local copy is restored.
The two-wrapper cap is a capability boundary, not a pinned rustc limit. -/
private def receiverSource (id : TypeId) :
    RuntimeArrayTypes.CompilerM (TypeId × TypeId × Option Miri.MIR.Mutability) := do
  match ← constructor id with
  | .rawPointer child _ => pure (id,child,none)
  | .reference child mutability _ => pure (id,child,some mutability)
  | .dynamic _ => do
    let pointer ← RuntimeArrayTypes.liftType (TypeArena.World.internType (.rawPointer id .Mut))
    pure (pointer,id,none)
  | .adt .. => do
    let terminal ← unwrapRawReceiver 3 id
    let .rawPointer child _ ← constructor terminal
      | throw "Virtual transparent receiver lost raw pointer terminal"
    pure (terminal,child,none)
  | _ => throw "Virtual receiver is outside the supported source families"

/-- All three families use pinned nullable raw physical Self layout. Only an
immediate source reference retains borrowed scalar-attribute classification. -/
def receiver (session : AbiSessionMaterial) (id : TypeId) :
    RuntimeArrayTypes.CompilerM (ArgAbi TypeId) := do
  let (logical,pointee,borrowed) ← receiverSource id
  unless (match ← constructor pointee with | .dynamic _ => true | _ => false) do
    throw "Virtual ABI receiver requires a dynamic pointee"
  let world ← get
  let thin ← liftPure (PrimitiveLayout.pointer world.metadata.target false none)
  let layout : TyAndLayout TypeId := ⟨logical,thin⟩
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

private def callerIntegerRecipe : Miri.MIR.IntegerKind → String
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .i128 => "i128" | .isize => "isize" | .u8 => "u8" | .u16 => "u16"
  | .u32 => "u32" | .u64 => "u64" | .u128 => "u128" | .usize => "usize"

/-- Audit the exact source-layout dependency closure before using a tracked
caller pointee size/alignment. Material FullLayout rows are residual answers,
never a replacement for an unavailable source recipe. -/
private def requireCallerSourceLayout : Nat → TypeId → RuntimeArrayTypes.CompilerM Unit
  | 0, _ => throw "Virtual tracked source layout dependency recursion exhausted"
  | fuel + 1, id => do
    let world ← get
    let key ← constructor id
    if let .material node ← liftPure (world.arena.lookupType id) then
      let some seed := world.metadata.source.layouts[node.layoutId]?
        | throw "Virtual tracked source layout seed absent"
      let exactRecipe := match key with
        | .adt .. => seed.structType == some id
        | .reference .. | .rawPointer .. => seed.pointerType == some id
        | .patternType .. => seed.patternType == some id
        | .str | .slice .. => seed.sequenceType == some id
        | .tuple .. => seed.tupleType == some id
        | .integer signed kind => signed == kind.signed && seed.primitiveRecipe == some (callerIntegerRecipe kind)
        | _ => false
      unless exactRecipe do
        throw "Virtual tracked caller-location source layout provider unavailable"
    match key with
    | .adt .. =>
      let declaration ← RuntimeArrayTypes.liftType (RuntimeMetadata.adtDeclarationInWorld world.metadata id)
      unless declaration.kind == .structKind do
        throw "Virtual tracked source layout ADT is not a struct"
      for field in declaration.fields do
        let child ← RuntimeArrayTypes.liftType
          (RuntimeMetadata.fieldTypeInWorld world.metadata id field.variantIndex field.fieldIndex)
        requireCallerSourceLayout fuel child
    | .reference child .. | .rawPointer child _ | .patternType child _ | .slice child =>
      requireCallerSourceLayout fuel child
    | .tuple fields => for field in fields do requireCallerSourceLayout fuel field
    | .integer .. | .str => pure ()
    | _ => throw "Virtual tracked source layout dependency constructor unavailable"

/-- Pinned TyCtxt::caller_location_ty raw source identity. The optional primitive
key alone is insufficient: require &'static PanicLocation<'static>, with the
raw lang-item attribute and generic signature material. Layout and Freeze are
subsequent source queries, never defaults or imported FnAbi answers. -/
private def callerLocation : RuntimeArrayTypes.CompilerM TypeId := do
  let world ← get
  let some id := world.metadata.source.queries.primitives.callerLocationType
    | throw "Virtual tracked caller-location source type absent"
  let .reference pointee .Not .Static ← constructor id
    | throw "Virtual tracked caller-location type is not a static shared reference"
  let .adt definition #[.Lifetime .Static] ← constructor pointee
    | throw "Virtual tracked caller-location pointee lacks canonical static argument"
  let declaration ← RuntimeArrayTypes.liftType (RuntimeMetadata.adtDeclarationInWorld world.metadata pointee)
  unless declaration.langItem == some "panic_location" && declaration.kind == .structKind do
    throw "Virtual tracked caller-location raw lang-item identity mismatch"
  let reference ← liftPure (world.arena.definitionRef definition)
  let some raw := world.metadata.source.definitions[reference]?.bind (·.genericTemplate)
    | throw "Virtual tracked caller-location generic source absent"
  unless raw.parameters == #[.region] do
    throw "Virtual tracked caller-location raw generic header mismatch"
  requireCallerSourceLayout 256 id
  let term ← liftPure (GenericInstantiationWorld.ofType world.arena 16384 id)
  let erased ← liftPure (MirTemplate.eraseFreeRegions 16384 term)
  RuntimeArrayTypes.liftType (GenericInstantiationWorld.resolveType 16384 erased)

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
  let location ← if trackCaller then some <$> callerLocation else pure none
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
  let plan ← liftPure ((SignatureSeed.mk inputs output signature.abi signature.cVariadic).plan extra location tupleFields)
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
