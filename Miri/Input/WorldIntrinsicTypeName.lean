import Miri.Input.FunctionTypePrinter
import Miri.Input.WorldConstantName
import Miri.Input.RuntimeMetadata

/-! Pinned rustc_const_eval/util/type_name.rs mode. This printer has no diagnostic
session budget, visible-parent paths, trimming or verbose settings. -/
namespace Miri.Input.WorldIntrinsicTypeName
open TypeArena
private abbrev PrintM := StateT Nat WorldM
private def lift [Monad m] [MonadExceptOf String m] (value : Except String A) : m A :=
  match value with | .ok result => pure result | .error error => throw error
private def emit (text : String) : PrintM String := do
  let count ← get
  unless count + text.utf8ByteSize <= 100000 do throw "intrinsic type-name output exceeds supported budget"
  set (count + text.utf8ByteSize)
  pure text
private def integerName : MIR.IntegerKind → String
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .i128 => "i128" | .isize => "isize" | .u8 => "u8" | .u16 => "u16"
  | .u32 => "u32" | .u64 => "u64" | .u128 => "u128" | .usize => "usize"
private def sourcePath (material : DefinitionPath.Material) : Except String String := do
  let some root := material.components[0]? | throw "intrinsic raw definition path empty"
  unless root.kind == "crate_root" do throw "intrinsic raw definition path lacks crate root"
  let mut names := #[]
  for component in material.components do
    unless ["crate_root", "type", "value"].contains component.kind do
      throw "intrinsic definition namespace printing is not implemented"
    let some name := component.name | throw "intrinsic named path component lacks source symbol"
    if name.isEmpty then throw "intrinsic source path symbol empty"
    names := names.push name
  pure (String.intercalate "::" names.toList)
private def visit (metadata : RuntimeMetadata) : Nat → TypeId → PrintM String
  | 0, _ => throw "intrinsic type-name recursion exhausted"
  | fuel+1, id => do
    let world ← liftM (get : WorldM World)
    let constructor ← match ← lift (world.lookupType id) with
      | .constructed value => pure value
      | .material node =>
        let some value ← lift (world.materialKey node)
          | throw "intrinsic source type constructor printing is not implemented"
        pure value
    let child := visit metadata fuel
    let named := fun identity arguments => do
      let reference ← lift (world.definitionRef identity)
      let some definition := world.definitions[reference]? | throw "intrinsic named definition absent"
      let some path := definition.rawPath | throw "intrinsic named type requires raw definition path"
      unless path.parentParameterCount == 0 do throw "intrinsic nested generic path printing is not implemented"
      unless path.parameterDefaults.size == arguments.size do throw "intrinsic generic argument domain mismatch"
      if path.parameterDefaults.any (fun value => value) then
        throw "intrinsic generic default elision is not implemented"
      let mut result ← emit (← lift (sourcePath path))
      if !arguments.isEmpty then
        result := result ++ (← emit "<")
        for index in [:arguments.size] do
          if index > 0 then result := result ++ (← emit ", ")
          let some argument := arguments[index]? | throw "intrinsic generic argument absent"
          let text ← match argument with
            | .Type id => child id
            | .Lifetime _ => emit "'_"
            | .Const id => emit (← liftM (WorldConstantName.query id))
          result := result ++ text
        result := result ++ (← emit ">")
      pure result
    match constructor with
    | .bool => emit "bool" | .char => emit "char" | .str => emit "str" | .never => emit "!"
    | .integer _ kind => emit (integerName kind)
    | .float kind =>
      let name ← match kind with
        | .f16 => pure "f16" | .f32 => pure "f32" | .f64 => pure "f64" | .f128 => pure "f128"
        | _ => throw "intrinsic float spelling is not implemented"
      emit name
    | .adt identity arguments | .functionDefinition identity arguments #[] => named identity arguments
    | .functionDefinition _ _ _ => throw "intrinsic FnDef nonempty argument binder is not supported"
    | .foreign identity => named identity #[]
    | .functionPointer _ =>
      let term ← lift (GenericInstantiationWorld.ofType world (fuel + 1) id)
      let .node .type "function_pointer" "" (.cons signature .nil) := term
        | throw "function-pointer source signature absent"
      let printTerm := fun term => do
        let id ← liftM (GenericInstantiationWorld.resolveType fuel term)
        child id
      FunctionTypePrinter.render emit printTerm signature
    | .rawPointer pointee mutability =>
      let start ← emit (if mutability == .Mut then "*mut " else "*const ")
      pure (start ++ (← child pointee))
    | .reference pointee mutability region =>
      match region with
      | .Erased | .Static | .EarlyParameter .. => pure ()
      | _ => throw "intrinsic optional bound-region printing is not implemented"
      let start ← emit (if mutability == .Mut then "&mut " else "&")
      pure (start ++ (← child pointee))
    | .tuple elements =>
      let mut result ← emit "("
      for index in [:elements.size] do
        if index > 0 then result := result ++ (← emit ", ")
        let some element := elements[index]? | throw "intrinsic tuple element absent"
        result := result ++ (← child element)
      if elements.size == 1 then result := result ++ (← emit ",")
      pure (result ++ (← emit ")"))
    | .array element _ =>
      let count ← liftM (RuntimeMetadata.arrayCountInWorld metadata id)
      let start ← emit "["
      let inner ← child element
      pure (start ++ inner ++ (← emit ("; " ++ toString count.toNat ++ "]")))
    | .slice element =>
      let start ← emit "["
      let inner ← child element
      pure (start ++ inner ++ (← emit "]"))
    | _ => throw "intrinsic type-name source family is not implemented"
def query (metadata : RuntimeMetadata) (fuel : Nat) (id : TypeId) : WorldM String := do
  let (result,_) ← (visit metadata fuel id).run 0
  pure result
end Miri.Input.WorldIntrinsicTypeName
