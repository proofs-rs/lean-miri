import Miri.ABI.PackedExternAbi
import Miri.Input.Model
import Miri.Input.TypeArenaCheckedMaterial
import Miri.Input.RawFunctionSignature
import Miri.Input.PatternSyntax
import Miri.Input.DynamicPredicate
import Miri.Input.DefinitionPathHash

/-! The execution-owned type and constant constructor universe. Nodes store
one constructor plus existing child IDs; repeated children never duplicate a
nested Nat encoding. No compiler query answers, layouts, bodies, or normalization results are stored.
-/
namespace Miri.Input.TypeArena
open GenericSubstitution

/-- Raw FnPtr header plus child identities; no ABI query result is stored. -/
structure FunctionPointer where
  variables : Array GenericSubstitution.BoundVariable := #[]
  abiPacked : Nat
  safe : Bool
  cVariadic : Bool
  splatted : Option Nat
  inputs : Array TypeId
  output : TypeId
  deriving Repr, DecidableEq

inductive Constructor where
  | bool | char | str | never
  | integer (signed : Bool) (kind : MIR.IntegerKind)
  | float (kind : FloatTypeTag)
  | rawPointer (pointee : TypeId) (mutability : MIR.Mutability)
  | reference (pointee : TypeId) (mutability : MIR.Mutability) (region : MIR.Region)
  | patternType (base : TypeId) (pattern : CompilerPattern)
  | slice (element : TypeId)
  | tuple (elements : Array TypeId)
  | array (element : TypeId) (length : TypeConstantId)
  | adt (definition : DefinitionIdentity) (arguments : Array MIR.GenericArg)
  | foreign (definition : DefinitionIdentity)
  | functionDefinition (definition : DefinitionIdentity) (arguments : Array MIR.GenericArg)
      (variables : Array MIR.BoundVariableKind)
  | functionPointer (signature : FunctionPointer)
  | dynamic (value : DynamicPredicate.Dynamic)
  | closure (definition : DefinitionIdentity) (arguments : Array MIR.GenericArg)
  | coroutineClosure (definition : DefinitionIdentity) (arguments : Array MIR.GenericArg)
  | coroutine (definition : DefinitionIdentity) (arguments : Array MIR.GenericArg)
  | alias (kind : AliasTypeKind) (rigid : Bool) (definition : DefinitionIdentity)
      (arguments : Array MIR.GenericArg)
  deriving Repr, DecidableEq

/-- The two pools have separate dense namespaces. Material prefixes are never
changed; append-only constructor syntax belongs to one execution. -/
structure World where
  private mk ::
  materialTypes : Array TypeNode
  materialConstants : Array MIR.TypeConst
  definitions : Array DefinitionId
  materialPredicates : Array VtablePredicate
  pointerBytes : Nat
  checkedMaterial : CheckedMaterial materialTypes materialConstants definitions materialPredicates pointerBytes
  constructedTypes : Array Constructor := #[]
  constructedConstants : Array MIR.TypeConst := #[]

inductive TypeView where
  | material (node : TypeNode)
  | constructed (constructor : Constructor)

abbrev WorldM := StateT World (Except String)

def World.typeCount (world : World) : Nat := world.materialTypes.size + world.constructedTypes.size
def World.constantCount (world : World) : Nat := world.materialConstants.size + world.constructedConstants.size

def World.ofCheckedMaterial {types constants definitions predicates pointerBytes}
    (checked : CheckedMaterial types constants definitions predicates pointerBytes) : World := {
  materialTypes := types, materialConstants := constants, definitions, materialPredicates := predicates, pointerBytes,
  checkedMaterial := checked }

def World.ofMaterial (types : Array TypeNode) (constants : Array MIR.TypeConst)
    (definitions : Array DefinitionId) (predicates : Array VtablePredicate) (pointerBytes : Nat) : Except String World := do
  pure (World.ofCheckedMaterial (← CheckedMaterial.create types constants definitions predicates pointerBytes))

def World.ofDocument (document : ImportDocument) : Except String World := do
  let some target := document.runtimeTargetDataLayout
    | throw "type universe target material absent"
  World.ofMaterial document.types document.typeConstants document.definitions document.predicates
    target.defaultAddressSpacePointerSpec.pointerSizeBytes

def World.lookupType (world : World) (id : TypeId) : Except String TypeView := do
  if id < world.materialTypes.size then
    let some node := world.materialTypes[id]? | throw "type universe material node absent"
    unless node.id == id do throw "type universe material identity/index mismatch"
    pure (.material node)
  else
    let some constructor := world.constructedTypes[id - world.materialTypes.size]?
      | throw "type universe constructed node absent"
    pure (.constructed constructor)

def World.lookupConstant (world : World) (id : TypeConstantId) : Except String MIR.TypeConst :=
  if id < world.materialConstants.size then
    match world.materialConstants[id]? with
    | some value => .ok value | none => .error "type universe material constant absent"
  else match world.constructedConstants[id - world.materialConstants.size]? with
    | some value => .ok value | none => .error "type universe constructed constant absent"

def Constructor.shapeKind : Constructor → TypeShapeKind
  | .bool => .bool | .char => .char | .str => .str | .never => .never
  | .integer true _ => .int | .integer false _ => .uint | .float _ => .float
  | .rawPointer .. => .rawPointer | .reference .. => .reference | .slice .. => .slice
  | .patternType .. => .patternType
  | .tuple .. => .tuple | .array .. => .array | .adt .. => .adt | .foreign .. => .foreign
  | .functionDefinition .. => .functionDefinition | .functionPointer .. => .functionPointer
  | .dynamic .. => .dynamicTraitObject
  | .closure .. => .closure
  | .coroutineClosure .. => .coroutineClosure | .coroutine .. => .coroutine | .alias .. => .alias

def World.shapeKind (world : World) (id : TypeId) : Except String TypeShapeKind := do
  match ← world.lookupType id with
  | .material source => pure source.shapeKind
  | .constructed constructor => pure constructor.shapeKind

def World.identity (world : World) (id : DefinitionRef) : Except String DefinitionIdentity := do
  let some source := world.definitions[id]? | throw "type universe definition reference absent"
  pure ⟨source.crateIndex,source.index⟩

def World.definitionRef (world : World) (wanted : DefinitionIdentity) : Except String DefinitionRef := do
  world.checkedMaterial.definitionRef wanted

/-- Raw binder syntax retains all source sorts, even where an operation later
reports an explicit unsupported domain. -/
def World.boundVariable (world : World) : MIR.BoundVariableKind → Except String BoundVariable
  | .Const => pure .constant
  | .Type .Anon => pure (.type .anonymous)
  | .Type (.Param id) => return .type (.named (← world.identity id))
  | .Region kind => do
    let identity ← match kind with
      | .Anon => pure BoundIdentity.anonymous
      | .ClosureEnv => pure .closureEnvironment
      | .NamedForPrinting name => pure (.namedForPrinting name)
      | .Named id => do pure (BoundIdentity.named (← world.identity id))
    pure (.region identity)

def World.existential (world : World) (id : PredicateId) : Except String DynamicPredicate.Predicate := do
  let some source := world.materialPredicates[id]? | throw "dynamic source predicate is absent"
  let identity ← world.identity source.definitionId
  let body ← match source.kind with
    | .trait =>
      unless source.projectionTerm.isNone do throw "trait predicate has a projection term"
      pure (DynamicPredicate.Body.trait identity source.genericArgs)
    | .autoTrait =>
      unless source.genericArgs.isEmpty && source.projectionTerm.isNone do throw "auto trait predicate has arguments or term"
      pure (.autoTrait identity)
    | .projection =>
      let some term := source.projectionTerm | throw "dynamic projection source term is absent"
      pure (.projection identity source.genericArgs (match term with
        | .type id => .type id | .constant id => .constant id))
  pure ⟨← source.boundVariables.mapM world.boundVariable,body⟩

private def World.validateDynamic (world : World) (value : DynamicPredicate.Dynamic) : Except String Unit := do
  unless !value.predicates.isEmpty do throw "dynamic source predicate list is empty"
  unless regionReferencesValid world.definitions.size value.region do
    throw "dynamic object lifetime has an absent physical definition"
  let mut previous : Option DynamicPredicate.Body := none
  for predicate in value.predicates do
    let _ ← world.definitionRef predicate.body.definition
    for argument in predicate.body.arguments do
      if let .Lifetime region := argument then
        unless regionReferencesValid world.definitions.size region do
          throw "dynamic predicate lifetime has an absent physical definition"
    for boundVariable in predicate.variables do
      let identity := match boundVariable with
        | .region (.named identity) | .type (.named identity) => some identity
        | _ => none
      if let some identity := identity then
        let _ ← world.definitionRef identity
        pure ()
    if let some before := previous then
      unless before.rank ≤ predicate.body.rank do throw "dynamic source predicate order is invalid"
      if before.rank == predicate.body.rank && before.rank != 0 then
        let fingerprint := fun identity => do
          let reference ← world.definitionRef identity
          let some definition := world.definitions[reference]? | throw "dynamic predicate definition is absent"
          let some path := definition.rawPath | throw "dynamic ordering requires physical definition path"
          pure (← DefinitionPathHash.query path).toNat
        let left ← fingerprint before.definition
        let right ← fingerprint predicate.body.definition
        unless left % 2^64 < right % 2^64 ||
            (left % 2^64 == right % 2^64 && left / 2^64 ≤ right / 2^64) do
          throw "dynamic source predicate physical order is invalid"
    previous := some predicate.body

/-- Unsupported material families have no reconstructable identity key here.
FnPtr requires the complete raw header, including the splatted marker. -/
def World.materialKey (world : World) (source : TypeNode) : Except String (Option Constructor) := do
  match source.shape with
  | .bool => pure (some .bool) | .char => pure (some .char)
  | .str => pure (some .str) | .never => pure (some .never)
  | .int (.known kind) => pure (some (.integer true kind))
  | .uint (.known kind) => pure (some (.integer false kind))
  | .float kind => pure (some (.float kind))
  | .rawPointer child mutability => pure (some (.rawPointer child mutability))
  | .reference child mutability region => pure (some (.reference child mutability region))
  | .slice child => pure (some (.slice child))
  | .patternType base pattern => pure (some (.patternType base pattern))
  | .tuple children => pure (some (.tuple children))
  | .array child length _ => pure (some (.array child length))
  | .adt data => return some (.adt (← world.identity data.definition) data.args)
  | .foreign definition => return some (.foreign (← world.identity definition))
  | .functionPointer signature variables => do
    let mut boundVariables := #[]
    for variableKind in variables do
      let .Region kind := variableKind | return none
      let identity ← match kind with
        | .Anon => pure GenericSubstitution.BoundIdentity.anonymous
        | .ClosureEnv => pure .closureEnvironment
        | .NamedForPrinting name => pure (.namedForPrinting name)
        | .Named id => pure (.named (← world.identity id))
      boundVariables := boundVariables.push (.region identity)
    let some splatted := signature.rawSplatted | return none
    RawFunctionSignature.validateSplatted signature.inputs.size splatted
    pure (some (.functionPointer {
      variables := boundVariables
      abiPacked := Miri.ABI.ExternAbi.asPacked signature.abi
      safe := signature.safety == .Safe, cVariadic := signature.cVariadic, splatted,
      inputs := signature.inputs, output := signature.output }))
  | .dynamicTraitObject predicates principal region =>
    let values ← predicates.mapM world.existential
    let expected := predicates.find? (fun id => (world.materialPredicates[id]?).any (·.kind == .trait))
    unless principal == expected do throw "dynamic principal contradicts source predicate list"
    let value := DynamicPredicate.Dynamic.mk values region
    world.validateDynamic value
    pure (some (.dynamic value))
  | .functionDefinition definition args _ _ variables =>
    return some (.functionDefinition (← world.identity definition) args variables)
  | .closure definition args _ => return some (.closure (← world.identity definition) args)
  | .coroutineClosure definition args => return some (.coroutineClosure (← world.identity definition) args)
  | .coroutine definition args => return some (.coroutine (← world.identity definition) args)
  | .alias kind rigid definition args =>
    return some (.alias kind rigid (← world.identity definition) args)
  | _ => pure none

private def Constructor.arguments : Constructor → Array MIR.GenericArg
  | .adt _ args | .functionDefinition _ args _ | .alias _ _ _ args
  | .closure _ args | .coroutineClosure _ args | .coroutine _ args => args
  | _ => #[]

def Constructor.typeChildren (constructor : Constructor) : Array TypeId :=
  let direct := match constructor with
    | .rawPointer child _ | .reference child .. | .slice child | .array child _ => #[child]
    | .patternType base _ => #[base]
    | .tuple children => children
    | .functionPointer signature => signature.inputs.push signature.output
    | .dynamic value => value.predicates.foldl (fun acc predicate => acc ++ predicate.body.typeChildren) #[]
    | _ => #[]
  direct ++ constructor.arguments.filterMap (fun argument => match argument with
    | .Type id => some id | _ => none)

def Constructor.constantChildren (constructor : Constructor) : Array TypeConstantId :=
  let direct := match constructor with
    | .array _ length => #[length]
    | .patternType _ pattern => pattern.constantChildren
    | .dynamic value => value.predicates.foldl (fun acc predicate => acc ++ predicate.body.constantChildren) #[]
    | _ => #[]
  direct ++ constructor.arguments.filterMap (fun argument => match argument with
    | .Const id => some id | _ => none)

private def Constructor.definition : Constructor → Option DefinitionIdentity
  | .adt id _ | .foreign id | .functionDefinition id .. | .alias _ _ id _
  | .closure id _ | .coroutineClosure id _ | .coroutine id _ => some id
  | _ => none

private def World.validateConstructor (world : World) (constructor : Constructor) : Except String Unit := do
  if let .functionPointer signature := constructor then
    let _ ← Miri.ABI.ExternAbi.ofPacked signature.abiPacked
    RawFunctionSignature.validateSplatted signature.inputs.size signature.splatted
  if let .dynamic value := constructor then
    world.validateDynamic value
  for child in constructor.typeChildren do
    unless child < world.typeCount do throw "new type constructor references an absent type"
  for child in constructor.constantChildren do
    unless child < world.constantCount do throw "new type constructor references an absent constant"
  if let some identity := constructor.definition then
    let _ ← world.definitionRef identity
    pure ()

private def World.appendType (world : World) (constructor : Constructor) : TypeId × World :=
  (world.typeCount,{world with constructedTypes := world.constructedTypes.push constructor})

/-- Canonical syntax interning. Material reuse compares complete identity keys;
layouts, source spellings and diagnostic signatures never select a nominal type.
All matching material candidates are checked, preserving ambiguity rejection. -/
def World.internType (constructor : Constructor) : WorldM TypeId := do
  let world ← get
  world.validateConstructor constructor
  let mut found : Option TypeId := none
  for source in world.materialTypes do
    if (← world.materialKey source) == some constructor then
      unless found.isNone do throw "ambiguous canonical type universe material identity"
      found := some source.id
  for (source,index) in world.constructedTypes.zipIdx do
    if source == constructor then
      unless found.isNone do throw "duplicate canonical type universe constructor"
      found := some (world.materialTypes.size + index)
  if let some id := found then return id
  let (id,next) := world.appendType constructor
  set next
  pure id

/-- Constant interning retains raw typed constant syntax, not evaluation results.
The caller must provide an already-constructed type/constant graph. -/
def World.internConstant (constant : MIR.TypeConst) : WorldM TypeConstantId := do
  let world ← get
  let mut typeRefs := #[]
  let mut constantRefs := #[]
  let mut arguments := #[]
  match constant with
  | .Param _ _ declared => typeRefs := declared.toArray
  | .Value ty tree =>
    typeRefs := #[ty]
    unless tree.root < tree.nodes.size do throw "new constant valtree root is absent"
    for node in tree.nodes do
      match node with
      | .Leaf bits bytes =>
        unless bytes > 0 && bytes ≤ 16 && bits < 2^(8 * bytes) do
          throw "new constant scalar width is invalid"
      | .Branch children => constantRefs := constantRefs ++ children
  | .Alias _ _ definition args =>
    unless definition < world.definitions.size do throw "new constant alias definition is absent"
    arguments := args
  | .Expr _ args => arguments := args
  | .Error => throw "error constant cannot be interned"
  | _ => pure ()
  for argument in arguments do
    match argument with
    | .Type id => typeRefs := typeRefs.push id
    | .Const id => constantRefs := constantRefs.push id
    | .Lifetime _ => pure ()
  for id in typeRefs do
    unless id < world.typeCount do throw "new constant references an absent type"
  for id in constantRefs do
    unless id < world.constantCount do throw "new constant references an absent constant"
  let mut found := none
  for (value,index) in world.materialConstants.zipIdx do
    if value == constant then
      unless found.isNone do throw "ambiguous canonical type universe constant"
      found := some index
  for (value,index) in world.constructedConstants.zipIdx do
    if value == constant then
      unless found.isNone do throw "duplicate canonical type universe constant"
      found := some (world.materialConstants.size + index)
  if let some id := found then return id
  let id := world.constantCount
  set {world with constructedConstants := world.constructedConstants.push constant}
  pure id

theorem World.appendType_material_preserved (world : World) (constructor : Constructor) :
    (world.appendType constructor).2.materialTypes = world.materialTypes := rfl

theorem World.appendType_dense_id (world : World) (constructor : Constructor) :
    (world.appendType constructor).1 = world.materialTypes.size + world.constructedTypes.size := rfl

theorem World.appendType_count (world : World) (constructor : Constructor) :
    (world.appendType constructor).2.typeCount = world.typeCount + 1 := by
  simp [World.appendType, World.typeCount, Nat.add_assoc]

theorem World.appendType_lookup (world : World) (constructor : Constructor) :
    (world.appendType constructor).2.lookupType (world.appendType constructor).1 =
      .ok (.constructed constructor) := by
  simp [World.appendType, World.lookupType, World.typeCount,
    Nat.not_lt.mpr (Nat.le_add_right world.materialTypes.size world.constructedTypes.size),
    pure, Except.pure]

end Miri.Input.TypeArena
