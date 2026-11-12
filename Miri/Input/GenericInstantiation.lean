import Miri.Input.Model
import Miri.Input.TypeArena
import Miri.Input.GenericSubstitution
import Lean.Data.Json.Parser

/-! Bridge canonical generic trees to this execution's type universe. Exact
compiler identities and source structure establish equality. Layouts, names and
representation compatibility never select a type. Unsupported reconstructions
remain errors; the lazy arena supports only its actual constructor families. -/
namespace Miri.Input.GenericInstantiation
open GenericSubstitution

structure Context where
  types : Array TypeNode
  definitions : Array DefinitionId
  constants : Array MIR.TypeConst
  pointerBytes : Nat

def Context.ofDocument (source : ImportDocument) : Except String Context := do
  let some target := source.runtimeTargetDataLayout | throw "generic instantiation target material absent"
  let pointerBytes := target.defaultAddressSpacePointerSpec.pointerSizeBytes
  unless pointerBytes > 0 do throw "generic instantiation target pointer width is zero"
  TypeArena.validateMaterial source.types
  pure ⟨source.types, source.definitions, source.typeConstants, pointerBytes⟩

def identity (context : Context) (id : DefinitionRef) : Except String DefinitionIdentity := do
  let some source := context.definitions[id]? | throw "generic material definition absent"
  pure ⟨source.crateIndex, source.index⟩

def definitionRef (context : Context) (wanted : DefinitionIdentity) : Except String DefinitionRef := do
  let matching := context.definitions.zipIdx.filter fun (source, _) =>
    source.crateIndex == wanted.crateIndex && source.index == wanted.index
  unless matching.size == 1 do throw "generic physical definition material absent or duplicated"
  let some (_, id) := matching[0]? | throw "generic physical definition material absent"
  pure id

private def boundRegion (context : Context) : MIR.BoundRegionKind → Except String BoundIdentity
  | .Anon => pure .anonymous
  | .NamedForPrinting name => pure (.namedForPrinting name)
  | .Named id => return .named (← identity context id)
  | .ClosureEnv => pure .closureEnvironment

def ofRegion (context : Context) : MIR.Region → Except String Term
  | .EarlyParameter index _ => pure (.parameter .region index)
  | .Bound index variableIndex kind => return .bound .region index variableIndex (← boundRegion context kind)
  | .Placeholder scope variableIndex kind => return .placeholder .region scope variableIndex (← boundRegion context kind)
  | .Static => pure (.atom .region "static" "")
  | .Erased => pure (.atom .region "erased" "")
  | .InferenceVariable variableIndex => pure (.inference .region variableIndex)
  | .LateParameter scope kind => do
    let child ← match kind with
      | .Anon index => pure (.atom .region "anonymous" (toString index))
      | .NamedAnon index name => pure (.node .region "named_anonymous" (toString index)
          (Terms.ofArray #[Term.atom .region "printing_name" name]))
      | .Named id => do
        let definition ← identity context id
        pure (.definition .region "named" definition .nil)
      | .ClosureEnv => pure (.atom .region "closure_environment" "")
    return .definition .region "late_parameter" (← identity context scope) (.cons child .nil)
  | .Error => .error "error region in generic instantiation"

private def integerName : MIR.IntegerKind → String
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .i128 => "i128" | .isize => "isize" | .u8 => "u8" | .u16 => "u16"
  | .u32 => "u32" | .u64 => "u64" | .u128 => "u128" | .usize => "usize"

private def scalar (bits bytes : Nat) : Term :=
  .atom .aggregate "scalar" ("{\"bytes\":" ++ toString bytes ++ ",\"bits\":" ++ toString bits ++ "}")

mutual
def ofType (context : Context) : Nat → TypeId → Except String Term
  | 0, _ => .error "runtime type to generic tree traversal exhausted"
  | fuel + 1, id => do
    let source ← TypeArena.node context.types id context.constants.size
    let child := ofType context fuel
    let args := ofArguments context fuel
    match source.shape with
    | .bool => pure (.atom .type "bool" "")
    | .char => pure (.atom .type "char" "")
    | .str => pure (.atom .type "str" "")
    | .never => pure (.atom .type "never" "")
    | .int (.known kind) => pure (.atom .type "int" (integerName kind))
    | .uint (.known kind) => pure (.atom .type "uint" (integerName kind))
    | .float kind =>
      let name ← match kind with
        | .f16 => pure "f16" | .f32 => pure "f32" | .f64 => pure "f64" | .f128 => pure "f128"
        | _ => throw "floating type has no corresponding pinned rustc generic constructor"
      pure (.atom .type "float" name)
    | .rawPointer pointee mutability => do
      let target ← child pointee
      pure (.node .type "raw_pointer" (if mutability == .Mut then "mutable" else "immutable") (.cons target .nil))
    | .reference pointee mutability region => do
      let target ← child pointee
      let region ← ofRegion context region
      pure (.node .type "reference" (if mutability == .Mut then "mutable" else "immutable") (.cons region (.cons target .nil)))
    | .slice element => return .node .type "slice" "" (.cons (← child element) .nil)
    | .tuple elements => return .node .type "tuple" "" (Terms.ofArray (← elements.mapM child))
    | .array element length constructor =>
      let length ← if length < context.constants.size then ofConstant context fuel length else do
        unless id ≥ context.types.size && constructor.canonicalValueConstructor do
          throw "array length constant material absent"
        pure (.node .constant "value" "" (.cons (.atom .type "uint" "usize")
          (.cons (scalar constructor.count context.pointerBytes) .nil)))
      return .node .type "array" "" (.cons (← child element) (.cons length .nil))
    | .adt data => do
      let arguments ← args data.args
      return .definition .type "adt" (← identity context data.definition) (Terms.ofArray arguments)
    | .foreign definition => return .definition .type "foreign" (← identity context definition) .nil
    | .closure definition arguments _ => do
      let arguments ← args arguments
      return .definition .type "closure" (← identity context definition) (Terms.ofArray arguments)
    | .coroutineClosure definition arguments => do
      let arguments ← args arguments
      return .definition .type "coroutine_closure" (← identity context definition) (Terms.ofArray arguments)
    | .coroutine definition arguments => do
      let arguments ← args arguments
      return .definition .type "coroutine" (← identity context definition) (Terms.ofArray arguments)
    | _ => throw "runtime type lacks lossless generic tree reconstruction material"

def ofArgument (context : Context) : Nat → MIR.GenericArg → Except String Term
  | 0, _ => .error "runtime generic argument traversal exhausted"
  | fuel + 1, .Type id => ofType context fuel id
  | _ + 1, .Lifetime region => ofRegion context region
  | fuel + 1, .Const id => ofConstant context fuel id

def ofArguments (context : Context) : Nat → Array MIR.GenericArg → Except String (Array Term)
  | 0, _ => .error "runtime generic argument array traversal exhausted"
  | fuel + 1, args => args.mapM (ofArgument context fuel)

def ofConstant (context : Context) : Nat → TypeConstantId → Except String Term
  | 0, _ => .error "runtime generic constant traversal exhausted"
  | fuel + 1, id => do
    let some source := context.constants[id]? | throw "runtime generic constant material absent"
    match source with
    | .Param index _ _ => pure (.parameter .constant index)
    | .Bound index variableIndex => pure (.bound .constant index variableIndex .anonymous)
    | .Placeholder scope variableIndex => pure (.placeholder .constant scope variableIndex .anonymous)
    | .Value ty tree =>
      let some root := tree.nodes[tree.root]? | throw "generic constant valtree root absent"
      let value ← match root with
        | .Leaf bits bytes => pure (scalar bits bytes)
        | .Branch children => do
          let values ← children.mapM (ofConstant context fuel)
          pure (.node .aggregate "valtree_branch" "" (Terms.ofArray values))
      return .node .constant "value" "" (.cons (← ofType context fuel ty) (.cons value .nil))
    | _ => throw "runtime generic constant constructor is not reconstructed"
end

def resolveType (context : Context) : Nat → Term → Except String TypeId
  | 0, _ => .error "generic tree to runtime type traversal exhausted"
  | fuel + 1, term => do
    unless term.sort == .type do throw "generic type resolver received a non-type term"
    TypeArena.validateMaterial context.types
    let mut matching := #[]
    for source in context.types do
      match ofType context (fuel + 1) source.id with
      | .ok actual => if actual == term then matching := matching.push source.id
      | .error _ => pure () -- Other unsupported source families are not candidates.
    if let some first := matching[0]? then
      unless matching.all (· == first) do throw "ambiguous canonical generic type identity"
      return first
    match term with
    | .node .type "raw_pointer" "mutable" (.cons child .nil) =>
      TypeArena.intern context.types (← resolveType context fuel child) false
    | .node .type "reference" "mutable" (.cons (.atom .region "erased" "") (.cons child .nil)) =>
      TypeArena.intern context.types (← resolveType context fuel child) true
    | .node .type "array" "" (.cons child (.cons (.node .constant "value" ""
        (.cons (.atom .type "uint" "usize") (.cons (.atom .aggregate "scalar" payload) .nil))) .nil)) =>
      let raw ← Lean.Json.parse payload
      let bytes ← (← raw.getObjVal? "bytes").getNat?
      let bits ← (← raw.getObjVal? "bits").getNat?
      unless bytes == context.pointerBytes && bits < 2^(8 * bytes) && bits < 2^64 do
        throw "generic array length is not a canonical target usize"
      TypeArena.internArray context.types (← resolveType context fuel child) (UInt64.ofNat bits)
    | _ => throw "generic type constructor absent from material and lazy arena"

def definitionMaterial (context : Context) (id : DefinitionRef) : Except String DefinitionTemplate := do
  let some source := context.definitions[id]? | throw "generic definition material identity absent"
  let some material := source.genericTemplate | throw "generic definition source template absent"
  pure material

/-- Instantiate raw declaration material on demand. No exported
monomorphization result is consulted. The returned tree may still contain an
alias; normalization and trait selection remain separate operations. -/
def instantiateDefinitionType (context : Context) (fuel : Nat) (id : DefinitionRef)
    (arguments : Array MIR.GenericArg) : Except String Term := do
  let material ← definitionMaterial context id
  material.instantiateType fuel (← ofArguments context fuel arguments)

def instantiateDefinitionSignature (context : Context) (fuel : Nat) (id : DefinitionRef)
    (arguments : Array MIR.GenericArg) : Except String Term := do
  let material ← definitionMaterial context id
  material.instantiateSignature fuel (← ofArguments context fuel arguments)

def instantiateFieldType (context : Context) (fuel : Nat) (id : DefinitionRef)
    (arguments : Array MIR.GenericArg) (variantIndex fieldIndex : Nat) : Except String Term := do
  let material ← definitionMaterial context id
  material.instantiateField fuel (← ofArguments context fuel arguments) variantIndex fieldIndex

end Miri.Input.GenericInstantiation
