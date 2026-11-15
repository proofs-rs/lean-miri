import Miri.Input.Model.SourceTypes

namespace Miri.Input.SourceTypes
private def regionValue (material : Material) (contexts : Array (Array BoundVariable)) : Region → Except String MIR.Region
  | .static => pure .Static
  | .erased => pure .Erased
  | .earlyParameter _ => throw "Unsupported uninstantiated early source region"
  | .unsupported tag => throw s!"Unsupported source region {tag}"
  | .bound depth slot kind => do
    let some context := contexts[depth]? | throw "Unsupported source region binder depth"
    let some (.region expected) := context[slot]? | throw "Invalid source bound region slot"
    unless kind == expected do throw "Invalid source bound region identity"
    if let .named definition := kind then
      let some row := material.definitions[definition]? | throw "Invalid named region definition"
      unless row.kind == "LifetimeParam" do throw "Invalid named region declaration kind"
    return .Erased

/-- Instantiate source references without compiler queries. A binder supplied by
an actual source signature permits checked lifetime erasure at this boundary. -/
private def instantiateCore (material : Material) (types : Array (Option Concrete)) (constants : Array (Option Nat))
    (id : TypeRef) (contexts : Array (Array BoundVariable)) : Except String Concrete :=
  go 1024 #[] contexts id
where
  go (fuel : Nat) (seen : Array Nat) (contexts : Array (Array BoundVariable)) (id : Nat) : Except String Concrete := do
    let .succ fuel := fuel | throw "Unsupported source type recursion exhausted"
    unless !seen.contains id do throw "Invalid cyclic source type references"
    let some expr := material.types[id]? | throw "Invalid source type reference"
    let seen := seen.push id
    match expr with
    | .primitive kind name => return .primitive kind name
    | .parameter index _ =>
      let some value := types[index]?.join | throw "Unsupported unbound source type parameter"
      return value
    | .array element length =>
      let count ← match length with
        | .value typeRef bits size => do
          let some (.primitive "uint" "usize") := material.types[typeRef]?
            | throw "Unsupported array length scalar type"
          unless size > 0 && bits < 2^(size*8) do throw "Invalid array length scalar width"
          pure bits
        | .parameter index _ =>
          let some value := constants[index]?.join | throw "Unsupported unbound source const parameter"
          pure value
        | .alias reference => do
          let some alias := material.constantAliases[reference]? | throw "Invalid source const alias reference"
          let some value := alias.usizeValue | throw "Unsupported source array const alias compiler value unavailable"
          pure value
        | .unsupported tag => throw s!"Unsupported source array constant {tag}"
      return .array (← go fuel seen contexts element) count
    | .tuple elements => return .tuple (← elements.mapM (go fuel seen contexts))
    | .rawPointer pointee mutable =>
      return .pointer (if mutable == .Mut then "raw_pointer_mut" else "raw_pointer_const") (← go fuel seen contexts pointee)
    | .reference pointee mutable region =>
      let region ← regionValue material contexts region
      return .pointer s!"reference_{if region == .Static then "static" else "erased"}_{if mutable == .Mut then "mut" else "const"}"
        (← go fuel seen contexts pointee)
    | .patternNotNull base => return .patternNotNull (← go fuel seen contexts base)
    | .patternRange base lower upper =>
      let bound : PatternBound → Except String Nat := fun value => do
        match value with
        | .constant (.value _ bits _) => pure bits
        | .constant (.parameter index _) =>
          let some value := constants[index]?.join | throw "Unsupported unbound source pattern range parameter"
          pure value
        | _ => throw "Unsupported source pattern range bound witness unavailable"
      return .patternRange (← go fuel seen contexts base) (← bound lower) (← bound upper)
    | .nominal definition arguments =>
      return .nominal definition (← argumentTypes fuel seen contexts arguments)
    | .closure source =>
      unless source.arguments.size == source.parentCount + 3 do throw "Invalid closure synthetic argument count"
      for (ref,ordinal) in #[(source.kindType,0),(source.signatureType,1),(source.tupledUpvarsType,2)] do
        unless source.arguments[source.parentCount+ordinal]? == some (.type ref) do
          throw "Invalid closure synthetic argument identity"
      return .closure source.definition (← argumentTypes fuel seen contexts source.arguments)
    | .functionPointer sig =>
      unless sig.boundVariables.isEmpty do throw "Unsupported higher-ranked function pointer identity"
      let contexts := #[sig.boundVariables] ++ contexts
      return .functionPointer (← sig.inputs.mapM (go fuel seen contexts)) (← go fuel seen contexts sig.output)
        sig.safety sig.abi sig.cVariadic
    | .dynamicObject region predicates =>
      let region ← regionValue material contexts region
      let mut principal := none
      let mut arguments := #[]
      let mut projections := #[]
      let mut autoTraits := #[]
      for p in predicates do
        match p with
        | .trait definition args bound =>
          unless principal.isNone && projections.isEmpty && autoTraits.isEmpty && bound.isEmpty do
            throw "Unsupported existential principal/binder order"
          let some declaration := material.definitions[definition]? | throw "Invalid existential trait definition"
          unless declaration.kind == "Trait" && declaration.traitIsAuto == some false do
            throw "Invalid existential principal trait declaration"
          principal := some definition
          arguments ← argumentTypes fuel seen contexts args
        | .projection definition parent args term bound =>
          unless principal.isSome && autoTraits.isEmpty && bound.isEmpty do
            throw "Unsupported existential projection parent/binder"
          let some declaration := material.definitions[parent]? | throw "Invalid existential projection parent"
          unless declaration.kind == "Trait" do throw "Invalid existential projection parent category"
          projections := projections.push ⟨definition,parent,← argumentTypes fuel seen contexts args,← go fuel seen contexts term⟩
        | .autoTrait definition bound =>
          unless bound.isEmpty && !autoTraits.contains definition do throw "Unsupported existential auto-trait binder/duplicate"
          let some declaration := material.definitions[definition]? | throw "Invalid existential auto trait definition"
          unless declaration.kind == "Trait" && declaration.traitIsAuto == some true do
            throw "Invalid existential auto trait declaration"
          autoTraits := autoTraits.push definition
        | .unsupported tag => throw s!"Unsupported existential source predicate {tag}"
      return .dynamicObject ⟨region,principal,arguments,projections,autoTraits⟩
    | .functionDefinition .. => throw "Unsupported source function-definition type requires declared signature"
    | .projectionAlias .. => throw "Unsupported source associated type projection normalization"
    | .unsupported tag => throw s!"Unsupported source type {tag}"
  argumentTypes (fuel : Nat) (seen : Array Nat) (contexts : Array (Array BoundVariable))
      (arguments : Array Argument) : Except String (Array Concrete) := do
    let mut result := #[]
    for argument in arguments do
      let .type id := argument | throw "Unsupported nominal/closure non-type generic argument"
      result := result.push (← go fuel seen contexts id)
    return result

/-- Instantiate only supported concrete identities. A bound FnPtr must use the
original signature factory; erasing its binder would change type identity. -/
def instantiate (material : Material) (types : Array (Option Concrete)) (constants : Array (Option Nat))
    (id : TypeRef) (binder : Array BoundVariable := #[]) : Except String Concrete :=
  instantiateCore material types constants id #[binder]

/-- Context stack for original nested signatures. Bound references may be
instantiated for their layout while the signature factory retains their identity. -/
def instantiateInContext (material : Material) (types : Array (Option Concrete)) (constants : Array (Option Nat))
    (id : TypeRef) (contexts : Array (Array BoundVariable)) : Except String Concrete :=
  instantiateCore material types constants id contexts

/-- Runtime normalization erases source regions while preserving every other
structural identity. It does not solve aliases or trait obligations. -/
def eraseRegions (ty : Concrete) : Except String Concrete := go 1024 ty
where
  go (fuel : Nat) (ty : Concrete) : Except String Concrete := do
    let .succ fuel := fuel | throw "Unsupported source erasure recursion exhausted"
    match ty with
    | .primitive kind name => return .primitive kind name
    | .array t n => return .array (← go fuel t) n
    | .tuple ts => return .tuple (← ts.mapM (go fuel))
    | .nominal d ts => return .nominal d (← ts.mapM (go fuel))
    | .closure d ts => return .closure d (← ts.mapM (go fuel))
    | .patternNotNull t => return .patternNotNull (← go fuel t)
    | .patternRange t lower upper => return .patternRange (← go fuel t) lower upper
    | .pointer kind t =>
      let kind := match kind with
        | "reference_static_const" => "reference_erased_const"
        | "reference_static_mut" => "reference_erased_mut"
        | other => other
      return .pointer kind (← go fuel t)
    | .functionPointer inputs output safety abi variadic =>
      return .functionPointer (← inputs.mapM (go fuel)) (← go fuel output) safety abi variadic
    | .dynamicObject source =>
      let projections ← source.projections.mapM fun p => do
        pure ⟨p.definition,p.parentTrait,← p.arguments.mapM (go fuel),← go fuel p.term⟩
      return .dynamicObject ⟨.Erased,source.principal,← source.arguments.mapM (go fuel),projections,source.autoTraits⟩
end Miri.Input.SourceTypes

namespace Miri.Input.SourceTypes
/-- Validate source table identities/references at ingestion; unsupported semantic
cases remain deferred. Binder scope itself is validated when a signature asks
for erasure, since a referenced type can occur under different binders. -/
def Material.validate (material : Material) : Except String Unit := do
  let t : Nat → Except String Unit := fun id => unless id < material.types.size do throw "Invalid source type reference"
  let d : Nat → Except String Unit := fun id => unless id < material.definitions.size do throw "Invalid source definition reference"
  let r : Region → Except String Unit := fun region => do
    if let Region.bound _ _ (.named id) := region then d id
  let c : ConstExpr → Except String Unit := fun value => do
    match value with
    | ConstExpr.value id _ size =>
      t id
      unless size > 0 do throw "Invalid zero-width source scalar constant"
    | .parameter _ (some id) => t id
    | .alias id => unless id < material.constantAliases.size do throw "Invalid source constant alias reference"
    | _ => pure ()
  let args : Array Argument → Except String Unit := fun values => do
    for value in values do
      match value with
      | Argument.type id => t id
      | .constant value => c value
      | .lifetime region => r region
  let bound : Array BoundVariable → Except String Unit := fun values => do
    for value in values do
      if let BoundVariable.region (.named id) := value then d id
  for alias in material.constantAliases do
    d alias.definition
    t alias.typeRef
    args alias.arguments
  for expr in material.types do
    match expr with
    | .primitive .. | .parameter .. | .unsupported _ => pure ()
    | .array id length => t id; c length
    | .tuple ids => for id in ids do t id
    | .rawPointer id _ | .patternNotNull id => t id
    | .patternRange id lower upper =>
      t id
      for value in #[lower,upper] do
        match value with
        | .constant value => c value
        | .alias _ _ definition values => d definition; args values
    | .reference id _ region => t id; r region
    | .nominal id values | .functionDefinition id values => d id; args values
    | .projectionAlias definition parent values =>
      d definition; d parent; args values
      let some associated := material.definitions[definition]? | throw "Invalid source associated definition reference"
      let some owner := material.definitions[parent]? | throw "Invalid source associated parent reference"
      unless associated.kind == "AssocTy" && owner.kind == "Trait" do
        throw "Invalid source projection associated declaration/parent kind"
    | .functionPointer sig =>
      for id in sig.inputs do t id
      t sig.output
      bound sig.boundVariables
    | .closure value =>
      d value.definition; d value.parentDefinition; args value.arguments
      t value.kindType; t value.signatureType; t value.tupledUpvarsType
    | .dynamicObject region predicates =>
      r region
      for predicate in predicates do
        match predicate with
        | .trait id values variables => d id; args values; bound variables
        | .autoTrait id variables => d id; bound variables
        | .projection id parent values term variables => d id; d parent; args values; t term; bound variables
        | .unsupported _ => pure ()
  let mut raw := #[]
  for definition in material.definitions do
    unless !raw.contains definition.raw do throw "Invalid duplicate raw source definition"
    raw := raw.push definition.raw
    if let some adt := definition.adt then
      for variant in adt.variants do
        if let some id := variant.definition then d id
        if let some constructor := variant.constructor then d constructor.definition
        if let .explicit id := variant.discriminant then d id
        for field in variant.fields do
          t field.typeRef
          if let some id := field.definition then d id
  if let some (.declarations metadata) := material.dynMetadata then
    for id in #[metadata.metadataType,metadata.pointeeTrait,metadata.metadataParent,
        metadata.dynamic.definition,metadata.nonnull.definition,metadata.phantom.definition] do d id
    if let .notNullRawForeign _ id := metadata.pointer then d id
end Miri.Input.SourceTypes
namespace Miri.Input.SourceTypes
/-- Array length values are target usize, including the retained byte width;
instantiation must not erase a malformed scalar-width/source-type mismatch. -/
def Material.validateTarget (material : Material) (pointerBits : Nat) : Except String Unit := do
  for expr in material.types do
    if let .array _ (.value typeRef _ bytes) := expr then
      unless bytes*8 == pointerBits do throw "Invalid source array length target usize width"
      let some ty := material.types[typeRef]? | throw "Invalid source array length type reference"
      match ty with
      | .primitive "uint" "usize" => pure ()
      | .unsupported _ => pure () -- actual normalization remains unavailable at demand
      | _ => throw "Invalid source array length is not usize"
end Miri.Input.SourceTypes
