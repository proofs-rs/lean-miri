import Miri.Input.WorldConstantName
import Miri.Input.RuntimeMetadata
import Miri.Input.FunctionTypePrinter

/-! Pinned diagnostic type printer. Structural constructors and local named
ADTs/FnDefs are printed from canonical raw definition paths and source templates.
Contextual truncation, visible external paths, generic defaults and nonempty
binders remain explicit boundaries. Intrinsic type_name uses a separate printer. -/
namespace Miri.Input.WorldTypeName
open TypeArena
private structure PrinterState where
  printedTypes : Nat := 0
  emittedBytes : Nat := 0
private abbrev PrintM := StateT PrinterState WorldM
private def lift [Monad m] [MonadExceptOf String m] (value : Except String A) : m A :=
  match value with | .ok result => pure result | .error error => throw error
private def emit (text : String) : PrintM String := do
  let state ← get
  unless state.emittedBytes + text.utf8ByteSize <= 100000 do
    throw "constructed type printer output exceeds supported budget"
  set {state with emittedBytes := state.emittedBytes + text.utf8ByteSize}
  pure text
private def enter (options : Catalog.PrintOptions) (truncatable : Bool) : PrintM Unit := do
  let state ← get
  if truncatable && state.printedTypes > options.typeLengthLimit then
    throw "constructed type printer requires contextual truncation"
  set {state with printedTypes := state.printedTypes + 1}
private def integerName : MIR.IntegerKind → String
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .i128 => "i128" | .isize => "isize" | .u8 => "u8" | .u16 => "u16"
  | .u32 => "u32" | .u64 => "u64" | .u128 => "u128" | .usize => "usize"

private def visit (metadata : RuntimeMetadata) (options : Catalog.PrintOptions) :
    Nat → TypeId → PrintM String
  | 0, _ => throw "constructed type printer recursion exhausted"
  | fuel + 1, id => do
    let world ← liftM (get : WorldM World)
    let view ← lift (world.lookupType id)
    let constructor ← match view with
      | .constructed value => pure value
      | .material source =>
        let some value ← lift (world.materialKey source)
          | throw "contextual source type printing requires an unported constructor"
        pure value
    let child := visit metadata options fuel
    match constructor with
    | .bool => enter options false; emit "bool"
    | .char => enter options false; emit "char"
    | .str => enter options false; emit "str"
    | .never => enter options false; emit "!"
    | .integer _ kind => enter options false; emit (integerName kind)
    | .float kind =>
      let name ← match kind with
        | .f16 => pure "f16" | .f32 => pure "f32" | .f64 => pure "f64" | .f128 => pure "f128"
        | _ => throw "constructed float type printer has no pinned source spelling"
      enter options false
      emit name
    | .functionPointer _ =>
      enter options true
      let term ← lift (GenericInstantiationWorld.ofType world (fuel + 1) id)
      let .node .type "function_pointer" "" (.cons signature .nil) := term
        | throw "function-pointer source signature absent"
      let printTerm := fun term => do
        let id ← liftM (GenericInstantiationWorld.resolveType fuel term)
        child id
      FunctionTypePrinter.render emit printTerm signature
    | .rawPointer pointee mutability =>
      enter options true
      let leadingText ← emit (if mutability == .Mut then "*mut " else "*const ")
      pure (leadingText ++ (← child pointee))
    | .reference pointee mutability region =>
      enter options true
      if options.verboseInternals then throw "verbose reference type printing is not implemented"
      let lifetime ← match region with
        | .Erased => pure "" | .Static => pure "'static "
        | _ => throw "constructed reference type printing requires its named-region source printer"
      let leadingText ← emit ("&" ++ lifetime ++ if mutability == .Mut then "mut " else "")
      pure (leadingText ++ (← child pointee))
    | .tuple elements =>
      if elements.isEmpty then return ← emit "()"
      enter options true
      let mut parts := #[← emit "("]
      for index in [:elements.size] do
        if index > 0 then parts := parts.push (← emit ", ")
        let some element := elements[index]? | throw "tuple printer element absent"
        parts := parts.push (← child element)
      if elements.size == 1 then parts := parts.push (← emit ",")
      parts := parts.push (← emit ")")
      pure (String.join parts.toList)
    | .array element _ =>
      enter options false
      let count ← liftM (RuntimeMetadata.arrayCountInWorld metadata id)
      let leadingText ← emit "["
      let element ← child element
      let suffix ← emit ("; " ++ toString count.toNat ++ "]")
      pure (leadingText ++ element ++ suffix)
    | .functionDefinition identity arguments variables =>
      enter options true
      unless variables.isEmpty do throw "FnDef printing requires an empty argument binder"
      unless identity.crateIndex == 0 do throw "external FnDef diagnostic paths are not implemented"
      let reference ← lift (world.definitionRef identity)
      let some definition := world.definitions[reference]? | throw "FnDef source definition absent"
      let some path := definition.rawPath | throw "FnDef printing requires raw definition path"
      let some safety := path.functionHeaderSafety
        | throw "FnDef printing requires raw local HIR header safety"
      unless path.parentParameterCount == 0 do throw "FnDef inherited generic paths are not implemented"
      unless path.parameterDefaults.size == arguments.size do throw "FnDef argument/header domain mismatch"
      if path.parameterDefaults.any (fun value => value) then
        throw "FnDef default argument elision is not implemented"
      let some template := definition.genericTemplate | throw "FnDef source signature template absent"
      let argumentsTerm ← lift (GenericInstantiationWorld.ofArguments world fuel arguments)
      let signature ← lift (template.instantiateSignature fuel argumentsTerm)
      let forceSafe := safety == .safeTargetFeatures
      let mut result ← if forceSafe then emit "#[target_feature(..)] " else pure ""
      let printTerm := fun term => do
        let id ← liftM (GenericInstantiationWorld.resolveType fuel term)
        child id
      result := result ++ (← FunctionTypePrinter.render emit printTerm signature forceSafe)
      result := result ++ (← emit " {")
      result := result ++ (← emit (← lift (DefinitionPath.localNamedPath path options.verboseInternals
        options.trimDiagnosticPaths options.trimmedDefPaths)))
      if !arguments.isEmpty then
        result := result ++ (← emit "::<")
        for index in [:arguments.size] do
          if index > 0 then result := result ++ (← emit ", ")
          let some argument := arguments[index]? | throw "FnDef argument absent"
          let text ← match argument with
            | .Type id => child id
            | .Lifetime .Static => emit "'static"
            | .Lifetime .Erased => emit "'_"
            | .Lifetime _ => throw "FnDef named lifetime printing is not implemented"
            | .Const id => emit (← liftM (WorldConstantName.query id))
          result := result ++ text
        result := result ++ (← emit ">")
      pure (result ++ (← emit "}"))
    | .adt identity arguments =>
      enter options true
      unless identity.crateIndex == 0 do
        throw "external definition printing requires visible-parent source rules"
      let reference ← lift (world.definitionRef identity)
      let some definition := world.definitions[reference]?
        | throw "named type definition is absent"
      let some declaration := definition.adtDeclaration
        | throw "named ADT printing requires raw declaration attributes"
      if declaration.langItem == some "field_representing_type" then
        throw "field-representing ADT printing is not implemented"
      let some path := definition.rawPath
        | throw "named ADT printing requires raw definition path"
      unless path.parentParameterCount == 0 do
        throw "nested generic definition-path printing is not implemented"
      unless path.parameterDefaults.size == arguments.size do
        throw "named ADT argument domain differs from declaration generic header"
      if path.parameterDefaults.any (fun value => value) then
        throw "definition-path default argument elision is not implemented"
      let name ← lift (DefinitionPath.localNamedPath path options.verboseInternals
        options.trimDiagnosticPaths options.trimmedDefPaths)
      let mut result ← emit name
      if !arguments.isEmpty then
        result := result ++ (← emit "<")
        for index in [:arguments.size] do
          if index > 0 then result := result ++ (← emit ", ")
          let some argument := arguments[index]? | throw "named ADT argument absent"
          let text ← match argument with
            | .Type id => child id
            | .Lifetime .Static => emit "'static"
            | .Lifetime .Erased => emit "'_"
            | .Lifetime _ => throw "named generic lifetime printing is not implemented"
            | .Const id => emit (← liftM (WorldConstantName.query id))
          result := result ++ text
        result := result ++ (← emit ">")
      pure result
    | .slice element =>
      enter options false
      let leadingText ← emit "["
      let element ← child element
      let suffix ← emit "]"
      pure (leadingText ++ element ++ suffix)
    | _ => throw "constructed named type requires the raw source definition-path printer"

def query (metadata : RuntimeMetadata) (fuel : Nat) (id : TypeId) : WorldM String := do
  if let .material source ← lift ((← get).lookupType id) then return source.display
  let some options := metadata.source.queries.session.printOptions
    | throw "constructed type printing requires raw compiler print options"
  let (result,_) ← (visit metadata options fuel id).run {}
  pure result

end Miri.Input.WorldTypeName
