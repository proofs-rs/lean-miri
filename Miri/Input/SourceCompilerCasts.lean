import Miri.Input.SourceCompilerWorld
import Miri.Input.RuntimeMetadata
import Miri.Interpreter.Cast

/-! Pure cast leaves over the current canonical World. `lockstepTails` follows
pinned rustc_middle/ty/util.rs::struct_lockstep_tails_raw: matching structs and
equal-length tuples descend through their final fields, and other pairs stop.
The source physical registry has already instantiated/erased supported fields;
an unresolved alias is rejected instead of guessing its normalization. -/
namespace Miri.Input.SourceCompilerCasts
open Miri.Interpreter
private def node (world : SourceCompilerWorld.World) (id : Nat) : Except String TypeNode := do
  let some value := world.canonical.types[id]? | throw "Invalid source cast type handle"
  unless value.id == id do throw "Invalid source cast type/index identity"
  return value

def typeInfo (runtime : RuntimeMetadata) (id : Nat) : Except String CastTypeInfo := do
  let value ← runtime.node id |>.mapError toString
  match value.shape with
  | .int (.known kind) | .uint (.known kind) => pure (.integer kind)
  | .float .f16 => pure (.floating .binary16) | .float .f32 => pure (.floating .binary32)
  | .float .f64 => pure (.floating .binary64) | .float .f128 => pure (.floating .binary128)
  | .bool => pure .boolean | .char => pure .character
  | .rawPointer pointee _ => pure (.rawPointer pointee)
  | .reference pointee .. => pure (.reference pointee)
  | .functionPointer .. => pure .fnPointer
  | .functionDefinition definition arguments .. => pure (.fnDefinition definition arguments)
  | .closure definition arguments count => pure (.closure definition arguments count)
  | .adt data => pure (.adt data.definition)
  | .tuple elements => pure (.tuple elements)
  | .slice element => pure (.slice element)
  | .array element .. =>
    let layout ← runtime.lookup id |>.mapError toString
    let .Array _ count := layout.layout.fields | throw "Invalid source array layout/count"
    pure (.array element count)
  | .dynamicTraitObject predicates .. => pure (.dynamic predicates)
  | _ => throw "Unsupported source cast type constructor"

/-- Shared references and explicit raw-pointer dereference follow their actual
canonical child. ADT/Box and other forms require a separate source role rule. -/
def builtinDeref (world : SourceCompilerWorld.World) (id : Nat) (explicit : Bool) : Except String (Option Nat) := do
  let result ← match (← node world id).shape with
    | .reference pointee .. => pure (some pointee)
    | .rawPointer pointee _ => pure (if explicit then some pointee else none)
    | .adt _ | .alias .. => throw "Unsupported source cast ADT/alias dereference"
    | _ => pure none
  if let some id := result then let _ ← node world id
  return result

def lockstepTails (world : SourceCompilerWorld.World) (source target : Nat) : Except String (Nat × Nat) :=
  go (world.canonical.types.size + 1) source target
where
  go (fuel source target : Nat) : Except String (Nat × Nat) := do
    let .succ fuel := fuel | throw "Invalid cyclic source lockstep tail graph"
    let a ← node world source
    let b ← node world target
    match a.shape,b.shape with
    | .alias ..,_ | _,.alias .. => throw "Unsupported source lockstep alias normalization"
    | .adt a,.adt b =>
      if a.definition == b.definition && a.kind == .structKind then
        unless b.kind == .structKind do throw "Invalid source struct definition kind conflict"
        let [av] := a.variants.toList | throw "Invalid source struct variant count"
        let [bv] := b.variants.toList | throw "Invalid source struct variant count"
        unless av.fields.size == bv.fields.size do throw "Invalid source struct field count conflict"
        match av.fields.back?,bv.fields.back? with
        | none,none => pure (source,target)
        | some af,some bf => go fuel af.typeId bf.typeId
        | _,_ => throw "Invalid source struct tail availability"
      else pure (source,target)
    | .tuple a,.tuple b =>
      if a.size == b.size then
        match a.back?,b.back? with
        | none,none => pure (source,target)
        | some a,some b => go fuel a b
        | _,_ => throw "Invalid source tuple tail availability"
      else pure (source,target)
    | _,_ => pure (source,target)

/-- Pinned struct_tail_with_normalize follows final struct/tuple fields and
unwraps pattern types. Canonical source fields are already normalized. -/
def structTail (world : SourceCompilerWorld.World) (id : Nat) : Except String Nat :=
  go (world.canonical.types.size + 1) id
where
  go (fuel id : Nat) : Except String Nat := do
    let .succ fuel := fuel | throw "Invalid cyclic source struct tail graph"
    match (← node world id).shape with
    | .adt data =>
      if data.kind == .structKind then
        let [variant] := data.variants.toList | throw "Invalid source struct tail variant count"
        if let some field := variant.fields.back? then go fuel field.typeId else pure id
      else pure id
    | .tuple elements => if let some tail := elements.back? then go fuel tail else pure id
    | .patternType inner _ => go fuel inner
    | .alias .. => throw "Unsupported source struct tail alias normalization"
    | _ => pure id

/-- Narrow structural no-parameter check. Unknown constructors/binders/constants
remain unsupported, including inputs whose aliases have not been normalized. -/
def ensureMonomorphic (world : SourceCompilerWorld.World) (id : Nat) : Except String Unit :=
  go (world.canonical.types.size + world.canonical.predicates.size + 1) #[] id
where
  args (fuel : Nat) (seen : Array Nat) (values : Array MIR.GenericArg) : Except String Unit := do
    for value in values do
      match value with
      | .Type id => go fuel seen id
      | .Lifetime .Static | .Lifetime .Erased => pure ()
      | .Const id =>
        let some (.Value _ tree) := world.canonical.typeConstants[id]? | throw "Unsupported source cast non-value const argument"
        unless tree.nodes.all (fun value => match value with | .Leaf .. => true | _ => false) do
          throw "Unsupported source cast aggregate const argument"
      | _ => throw "Unsupported source cast generic region argument"
  go (fuel : Nat) (seen : Array Nat) (id : Nat) : Except String Unit := do
    if seen.contains id then return
    let .succ fuel := fuel | throw "Invalid source cast type graph traversal"
    let value ← node world id
    let seen := seen.push id
    match value.shape with
    | .bool | .char | .int _ | .uint _ | .float _ | .str | .never | .foreign _ => pure ()
    | .rawPointer child _ | .slice child | .patternType child .notNull => go fuel seen child
    | .array child length _ =>
      args fuel seen #[.Const length]
      go fuel seen child
    | .reference child _ region =>
      unless region == .Static || region == .Erased do throw "Unsupported source cast bound/reference region"
      go fuel seen child
    | .tuple children => for child in children do go fuel seen child
    | .adt data => args fuel seen data.args
    | .closure _ values _ => args fuel seen values
    | .functionDefinition _ values signature bound =>
      args fuel seen values
      unless bound.isEmpty do throw "Unsupported source cast higher-ranked signature monomorphism"
      for child in signature.inputs.push signature.output do go fuel seen child
    | .functionPointer signature bound =>
      unless bound.isEmpty do throw "Unsupported source cast higher-ranked pointer monomorphism"
      for child in signature.inputs.push signature.output do go fuel seen child
    | .dynamicTraitObject predicates _ region =>
      unless region == .Static || region == .Erased do throw "Unsupported source cast bound object region"
      for id in predicates do
        let some predicate := world.canonical.predicates[id]? | throw "Invalid source cast predicate handle"
        unless predicate.boundVariables.isEmpty do throw "Unsupported source cast predicate binder"
        args fuel seen predicate.genericArgs
        if let some id := predicate.projectionTerm then go fuel seen id
    | _ => throw "Unsupported source cast monomorphism constructor"
end Miri.Input.SourceCompilerCasts
