import Miri.Input.Model
import Miri.Input.TypeArena
import Miri.Input.GenericSubstitution
import Lean.Data.Json.Parser

/-! Reification and lookup restricted to the immutable source type prefix. Exact
compiler identities and source structure establish equality. Layouts, names and
representation compatibility never select a type. Runtime construction uses
GenericInstantiationWorld and its explicitly threaded execution universe. -/
namespace Miri.Input.GenericInstantiation
open GenericSubstitution

structure Context where
  types : Array TypeNode
  definitions : Array DefinitionId
  constants : Array MIR.TypeConst
  pointerBytes : Nat
  /-- Input-bound validation evidence, never a compiler query result cache. -/
  denseTypes : Option (PLift (TypeArena.isDense types = true)) := none

def Context.ofDocument (source : ImportDocument) : Except String Context := do
  let some target := source.runtimeTargetDataLayout | throw "generic instantiation target material absent"
  let pointerBytes := target.defaultAddressSpacePointerSpec.pointerSizeBytes
  unless pointerBytes > 0 do throw "generic instantiation target pointer width is zero"
  if dense : TypeArena.isDense source.types = true then
    pure {
      types := source.types, definitions := source.definitions,
      constants := source.typeConstants, pointerBytes, denseTypes := some ⟨dense⟩ }
  else throw "material type ID/index mismatch"

def Context.node (context : Context) (id : TypeId) : Except String TypeNode :=
  match context.denseTypes with
  | some _ => TypeArena.materialNode context.types id
  | none => TypeArena.node context.types id

def Context.validateMaterial (context : Context) : Except String Unit :=
  match context.denseTypes with
  | some _ => pure ()
  | none => TypeArena.validateMaterial context.types

theorem Context.node_eq_checked (context : Context) (id : TypeId) :
    context.node id = TypeArena.node context.types id := by
  cases evidence : context.denseTypes with
  | none => simp [Context.node, evidence]
  | some certificate =>
    simp [Context.node, evidence, TypeArena.node, TypeArena.validateMaterial, certificate.down]

theorem Context.validateMaterial_eq (context : Context) :
    context.validateMaterial = TypeArena.validateMaterial context.types := by
  cases evidence : context.denseTypes with
  | none => simp [Context.validateMaterial, evidence]
  | some certificate =>
    simp [Context.validateMaterial, evidence, TypeArena.validateMaterial, certificate.down]

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
    let source ← context.node id
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
    | .array element length _ =>
      let length ← ofConstant context fuel length
      return .node .type "array" "" (.cons (← child element) (.cons length .nil))
    | .adt data => do
      let arguments ← args data.args
      return .definition .type "adt" (← identity context data.definition) (Terms.ofArray arguments)
    -- Pinned rustc_type_ir/src/ty_kind.rs:223: FnDef identity contains the
    -- definition and bound arguments. The separately exported signature binder
    -- is not the binder of those arguments.
    | .functionDefinition definition arguments _ _ argumentVariables => do
      unless argumentVariables.isEmpty do
        throw "function definition argument binder reconstruction is unsupported"
      let arguments ← args arguments
      return .definition .type "function_definition" (← identity context definition)
        (.cons (.binder #[] (.node .aggregate "arguments" "" (Terms.ofArray arguments))) .nil)
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
    | .alias kind rigid definition arguments => do
      let kind := match kind with
        | .projection => "projection" | .inherent => "inherent"
        | .opaque => "opaque" | .free => "free"
      let rigidity := if rigid then "rigid" else "not_rigid"
      let arguments ← args arguments
      return .definition .type ("alias_" ++ kind ++ "_" ++ rigidity)
        (← identity context definition) (Terms.ofArray arguments)
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

/-- Semantic outer constructor only. Unknown trees remain candidates. -/
def constructorOfTerm : Term → Option TypeShapeKind
  | .atom .type "bool" _ => some .bool
  | .atom .type "char" _ => some .char
  | .atom .type "int" _ => some .int
  | .atom .type "uint" _ => some .uint
  | .atom .type "float" _ => some .float
  | .atom .type "str" _ => some .str
  | .atom .type "never" _ => some .never
  | .node .type "raw_pointer" _ _ => some .rawPointer
  | .node .type "reference" _ _ => some .reference
  | .node .type "slice" _ _ => some .slice
  | .node .type "tuple" _ _ => some .tuple
  | .node .type "array" _ _ => some .array
  | .definition .type "adt" _ _ => some .adt
  | .definition .type "function_definition" _ _ => some .functionDefinition
  | .definition .type "foreign" _ _ => some .foreign
  | .definition .type "closure" _ _ => some .closure
  | .definition .type "coroutine_closure" _ _ => some .coroutineClosure
  | .definition .type "coroutine" _ _ => some .coroutine
  | .definition .type tag _ _ =>
    if ["alias_projection_rigid", "alias_projection_not_rigid",
        "alias_inherent_rigid", "alias_inherent_not_rigid",
        "alias_opaque_rigid", "alias_opaque_not_rigid",
        "alias_free_rigid", "alias_free_not_rigid"].contains tag then some .alias else none
  | _ => none

private def definitionOfShape : TypeShape → Option DefinitionRef
  | .adt data => some data.definition
  | .foreign id | .functionDefinition id .. | .closure id .. | .coroutineClosure id .. | .coroutine id ..
  | .alias _ _ id _ => some id
  | _ => none

/-- A necessary structural test, never sufficient type identity. Failed identity
material lookups remain candidates, so normal reconstruction retains its errors. -/
def mayMatch (context : Context) (source : TypeNode) (term : Term) : Bool :=
  let constructorMatches := match constructorOfTerm term with
    | none => true
    | some kind => kind == source.shape.kind
  constructorMatches && match term, definitionOfShape source.shape with
    | .definition .type _ wanted _, some id => match identity context id with
      | .ok actual => actual == wanted
      | .error _ => true
    | _, _ => true

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Every successful exact-source reconstruction survives the prefilter. In
particular, duplicate semantic candidates cannot be hidden by this optimization. -/
theorem mayMatch_ofType (context : Context) (source : TypeNode) (fuel : Nat)
    (term : Term) (node : context.node source.id = .ok source)
    (result : ofType context (fuel + 1) source.id = .ok term) :
    mayMatch context source term = true := by
  simp only [ofType, node, bind, Except.bind] at result
  cases shape : source.shape <;>
    simp [shape] at result
  all_goals simp only [pure, Except.pure] at result
  all_goals try { cases result; simp [mayMatch, constructorOfTerm, shape, TypeShape.kind] }
  all_goals repeat' first | split at result | cases result
  all_goals simp_all [mayMatch, constructorOfTerm, definitionOfShape, TypeShape.kind,
    throw, BEq.beq, instBEqDefinitionIdentity.beq]

def resolveType (context : Context) : Nat → Term → Except String TypeId
  | 0, _ => .error "generic tree to runtime type traversal exhausted"
  | fuel + 1, term => do
    unless term.sort == .type do throw "generic type resolver received a non-type term"
    context.validateMaterial
    let mut matching := #[]
    for source in context.types do
      if mayMatch context source term then
        match ofType context (fuel + 1) source.id with
        | .ok actual => if actual == term then matching := matching.push source.id
        | .error _ => pure () -- Other unsupported source families are not candidates.
    if let some first := matching[0]? then
      unless matching.all (· == first) do throw "ambiguous canonical generic type identity"
      return first
    match term with
    | .node .type "raw_pointer" "mutable" (.cons child .nil) =>
      TypeArena.findPointer context.types (← resolveType context fuel child) false
    | .node .type "reference" "mutable" (.cons (.atom .region "erased" "") (.cons child .nil)) =>
      TypeArena.findPointer context.types (← resolveType context fuel child) true
    | .node .type "array" "" (.cons child (.cons (.node .constant "value" ""
        (.cons (.atom .type "uint" "usize") (.cons (.atom .aggregate "scalar" payload) .nil))) .nil)) =>
      let raw ← Lean.Json.parse payload
      let bytes ← (← raw.getObjVal? "bytes").getNat?
      let bits ← (← raw.getObjVal? "bits").getNat?
      unless bytes == context.pointerBytes && bits < 2^(8 * bytes) && bits < 2^64 do
        throw "generic array length is not a canonical target usize"
      TypeArena.findArray context.types (← resolveType context fuel child) (UInt64.ofNat bits)
    | _ => throw "generic type constructor absent from source material"

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
