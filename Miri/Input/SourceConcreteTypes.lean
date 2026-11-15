import Miri.Input.SourceCompilerWorld
import Miri.Input.Model.SourceTypes

/-! Inversion of requested canonical arguments into typed source syntax. No
normalization, layout-equivalence identity or all-pool reconstruction occurs.
Callers must round-trip through source physical interning before using a type. -/
namespace Miri.Input.SourceConcreteTypes
open Miri.Interpreter
abbrev World := SourceCompilerWorld.World
private def integerName (kind : MIR.IntegerKind) (signed : Bool) : Except String String := do
  match signed,kind with
  | true,.i8 => pure "i8" | true,.i16 => pure "i16" | true,.i32 => pure "i32"
  | true,.i64 => pure "i64" | true,.i128 => pure "i128" | true,.isize => pure "isize"
  | false,.u8 => pure "u8" | false,.u16 => pure "u16" | false,.u32 => pure "u32"
  | false,.u64 => pure "u64" | false,.u128 => pure "u128" | false,.usize => pure "usize"
  | _,_ => throw "typed ABI integer kind/tag mismatch"

def scalarConstant (world : World) (width : Nat) (constant : Nat) : Except String (Nat × Nat × Nat) := do
  let some (.Value type tree) := world.canonical.typeConstants[constant]? | throw "typed ABI constant argument is not a value"
  let some row := world.canonical.types[type]? | throw "typed ABI constant type absent"
  unless row.id == type do throw "typed ABI constant type identity mismatch"
  match row.shape with
  | .uint (.known .usize) => pure ()
  | _ => throw "typed ABI constant argument requires usize"
  let [.Leaf bits bytes] := tree.nodes.toList | throw "typed ABI constant argument tree unsupported"
  unless tree.root == 0 && bytes*8 == width && bits < 2^width do throw "typed ABI constant argument width/range invalid"
  return (type,bits,bytes)

def concreteType (world : World) (width : Nat) (typeId : Nat) : Except String SourceTypes.Concrete :=
  go (world.canonical.types.size + 1) #[] typeId
where
  go (fuel : Nat) (active : Array Nat) (typeId : Nat) : Except String SourceTypes.Concrete := do
    let .succ fuel := fuel | throw "typed ABI argument type traversal exhausted"
    unless !active.contains typeId do throw "recursive typed ABI argument unsupported"
    let some row := world.canonical.types[typeId]? | throw "typed ABI argument type absent"
    unless row.id == typeId do throw "typed ABI argument type identity mismatch"
    let child := go fuel (active.push typeId)
    match row.shape with
    | .bool => pure (.primitive "bool" "")
    | .char => pure (.primitive "char" "")
    | .int (.known kind) => return .primitive "int" (← integerName kind true)
    | .uint (.known kind) => return .primitive "uint" (← integerName kind false)
    | .tuple fields => return .tuple (← fields.mapM child)
    | .rawPointer pointee mutable => return .pointer (if mutable == .Mut then "raw_pointer_mut" else "raw_pointer_const") (← child pointee)
    | .reference pointee mutable region =>
      let lifetime ← match region with
        | .Static => pure "static"
        | .Erased => pure "erased"
        | _ => throw "typed ABI reference bound/free region unsupported"
      return .pointer ("reference_" ++ lifetime ++ (if mutable == .Mut then "_mut" else "_const")) (← child pointee)
    | .dynamicTraitObject predicates principal region =>
      unless region == .Static || region == .Erased do throw "typed ABI dynamic region unsupported"
      let some material := world.canonical.sourceMaterial | throw "typed dynamic source absent"
      let some physical := material.physical | throw "typed dynamic physical source absent"
      let sourceDefinition (definition : Nat) : Except String Nat := do
        let some raw := world.canonical.definitions[definition]? | throw "typed dynamic raw definition absent"
        let rows := physical.definitions.toList.zipIdx |>.filter (fun (row,_) => row.raw == raw)
        let [(_,index)] := rows | throw "typed dynamic source definition absent/ambiguous"
        pure index
      let mut object : SourceTypes.Existential SourceTypes.Concrete := ⟨region,none,#[],#[],#[]⟩
      for id in predicates do
        let some predicate := world.canonical.predicates[id]? | throw "typed dynamic predicate absent"
        unless predicate.boundVariables.isEmpty do throw "typed dynamic bound predicate unsupported"
        let definition ← sourceDefinition predicate.definitionId
        let args : Array SourceTypes.Concrete ← predicate.genericArgs.mapM fun arg => do
          let .Type type := arg | throw "typed dynamic non-type argument unsupported"
          child type
        match predicate.kind with
        | .trait =>
          unless principal == some id && object.principal.isNone && predicate.projectionTerm.isNone do
            throw "typed dynamic principal identity mismatch"
          object := {object with principal := some definition, arguments := args}
        | .autoTrait =>
          unless args.isEmpty && predicate.projectionTerm.isNone do throw "typed dynamic auto trait arguments unsupported"
          object := {object with autoTraits := object.autoTraits.push definition}
        | .projection =>
          let some term := predicate.projectionTerm | throw "typed dynamic projection term absent"
          let mut parents : Array Nat := #[]
          for expression in physical.types do
            if let .dynamicObject _ sourcePredicates := expression then
              for sourcePredicate in sourcePredicates do
                if let .projection assoc parent _ _ _ := sourcePredicate then
                  if assoc == definition && !parents.contains parent then parents := parents.push parent
          let [parent] := parents.toList | throw "typed dynamic projection parent source absent/ambiguous"
          object := {object with projections := object.projections.push ⟨definition,parent,args,← child term⟩}
      unless principal.isSome == object.principal.isSome do throw "typed dynamic principal absent"
      return .dynamicObject object
    | .array element length constructor =>
      let (_,bits,_) ← scalarConstant world width length
      unless constructor.canonicalValueConstructor && constructor.count == bits do throw "typed ABI array count identity mismatch"
      return .array (← child element) bits
    | .closure definition arguments count =>
      let some raw := world.canonical.definitions[definition]? | throw "typed closure raw definition absent"
      let some material := world.canonical.sourceMaterial | throw "typed closure source material absent"
      let some physical := material.physical | throw "typed closure physical source absent"
      let declarations := physical.definitions.toList.zipIdx |>.filter (fun (row,_) => row.raw == raw)
      let [(declared,sourceDefinition)] := declarations | throw "typed closure source definition absent/ambiguous"
      unless declared.kind == "closure" do throw "typed closure source definition kind mismatch"
      let args : Array SourceTypes.Concrete ← arguments.mapM fun argument => do
        let .Type type := argument | throw "typed closure non-type generic argument unsupported"
        child type
      let some (.tuple captures) := args.back? | throw "typed closure upvar tuple absent"
      unless captures.size == count do throw "typed closure capture count mismatch"
      return .closure sourceDefinition args
    | .functionPointer signature binders =>
      unless binders.isEmpty && !signature.cVariadic do throw "typed ABI argument function binder/variadic unsupported"
      return .functionPointer (← signature.inputs.mapM child) (← child signature.output) signature.safety signature.abi false
    | _ => throw "typed ABI argument type constructor unsupported"

end Miri.Input.SourceConcreteTypes
