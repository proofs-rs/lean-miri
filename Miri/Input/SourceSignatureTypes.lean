import Miri.Input.SourcePhysical

/-! Original signature identities and their region-erased layout queries are
separate. Bound regions below a checked signature binder are never replaced by
an erased region in the resulting TypeShape. -/
namespace Miri.Input.SourceSignatureTypes
open SourceTypes

private def region (material : Material) (contexts : Array (Array BoundVariable))
    (world : SourceCompilerWorld.World) (value : Region) :
    Except String (SourceCompilerWorld.World × MIR.Region) := do
  match value with
  | .static => return (world,.Static)
  | .erased => return (world,.Erased)
  | .bound depth slot kind =>
    let some binder := contexts[depth]? | throw "Unsupported original signature region binder depth"
    unless binder[slot]? == some (.region kind) do
      throw "Unsupported original signature region binder slot/kind"
    let (world,kind) ← match kind with
      | .anonymous => pure (world,MIR.BoundRegionKind.Anon)
      | .namedForPrinting name => pure (world,.NamedForPrinting name)
      | .closureEnvironment => pure (world,.ClosureEnv)
      | .named definition => do
        let some row := material.definitions[definition]? | throw "Invalid signature named region definition"
        unless row.kind == "LifetimeParam" do throw "Invalid signature named region category"
        let (world,id) ← SourceCompilerWorld.internDefinition world row.raw
        pure (world,.Named id)
    return (world,.Bound (.Bound depth) slot kind)
  | .earlyParameter _ => throw "Unsupported original early signature region"
  | .unsupported tag => throw s!"Unsupported original signature region {tag}"

/-- Translate binder declarations through the same checked raw-definition map
used by signature references. -/
def boundVariables (initial : SourceCompilerWorld.World) (binder : Array BoundVariable) :
    Except String (SourceCompilerWorld.World × Array MIR.BoundVariableKind) := do
  let some source := initial.canonical.sourceMaterial | throw "Unsupported signature source unavailable"
  let some material := source.physical | throw "Unsupported signature types unavailable"
  let mut world := initial
  let mut result := #[]
  for (entry,slot) in binder.zipIdx do
    let .region kind := entry | throw "Unsupported original signature non-region binder"
    let (updated,value) ← region material #[binder] world (.bound 0 slot kind)
    world := updated
    let .Bound _ _ kind := value | throw "Invalid translated signature region binder"
    result := result.push (MIR.BoundVariableKind.Region kind)
  return (world,result)

/-- Construct source signature identity using the erased physical query only
for geometry. This domain supports primitive, tuple, array, pointer and
existential predicate trees, plus instantiated nominal types under an empty
signature binder; other constructors remain Unsupported rather than silently erase identity. -/
def intern (initial : SourceCompilerWorld.World) (bindings : Array (Option Concrete))
    (constants : Array (Option Nat)) (binder : Array BoundVariable) (reference : TypeRef)
    (canonicalBindings : Array (Option TypeId) := #[]) (eraseFreeRegions : Bool := false) :
    Except String (SourceCompilerWorld.World × TypeId) := go 1024 initial #[binder] reference
where
  go (fuel : Nat) (world : SourceCompilerWorld.World) (contexts : Array (Array BoundVariable)) (reference : TypeRef) :
      Except String (SourceCompilerWorld.World × TypeId) := do
    let .succ fuel := fuel | throw "Unsupported original signature recursion exhausted"
    let some source := world.canonical.sourceMaterial | throw "Unsupported signature source unavailable"
    let some material := source.physical | throw "Unsupported signature types unavailable"
    let some expr := material.types[reference]? | throw "Invalid signature type reference"
    -- Function-item generic arguments have exact canonical identities even
    -- though they are intentionally outside the layout-only Concrete syntax.
    if let .parameter index _ := expr then
      if let some id := canonicalBindings[index]?.join then
        unless (bindings[index]?.join).isNone do throw "Invalid conflicting signature bindings"
        let some node := world.canonical.types[id]? | throw "Invalid canonical signature binding"
        unless node.id == id do throw "Invalid canonical signature binding identity"
        let .functionDefinition .. := node.shape | throw "Invalid canonical function-item binding kind"
        let some _ := world.canonical.layouts[node.layoutId]? | throw "Invalid canonical function-item layout binding"
        return (world,id)
    if let .functionPointer signature := expr then
      let (world,variables) ← boundVariables world signature.boundVariables
      let mut world := world
      let mut inputs := #[]
      let nested := #[signature.boundVariables] ++ contexts
      for reference in signature.inputs do
        let (updated,id) ← go fuel world nested reference
        world := updated
        inputs := inputs.push id
      let (finished,output) ← go fuel world nested signature.output
      let layout ← SourcePhysical.functionPointerLayout (← SourcePhysical.target finished)
      SourceCompilerWorld.internType finished (.functionPointer
        ⟨inputs,output,signature.safety,signature.abi,signature.cVariadic⟩ variables) layout "source function pointer"
    else if let .nominal .. := expr then
      -- An independently closed nominal has no escaping binder to erase.
      -- Region-bearing nominal arguments remain unsupported by this factory.
      let closed ← instantiate material bindings constants reference
      let closed ← if eraseFreeRegions then eraseRegions closed else pure closed
      SourcePhysical.intern world closed
    else do
      let erased ← instantiateInContext material bindings constants reference contexts
      let erased ← if eraseFreeRegions then eraseRegions erased else pure erased
      let (world,erasedId) ← SourcePhysical.intern world erased
      let some erasedNode := world.canonical.types[erasedId]? | throw "Invalid erased signature type"
      let some layout := world.canonical.layouts[erasedNode.layoutId]? | throw "Invalid erased signature layout"
      let (world,shape) ← match expr with
        | .primitive .. | .parameter .. => pure (world,erasedNode.shape)
        | .reference pointee mutable value => do
          let (world,pointee) ← go fuel world contexts pointee
          let (updated,value) ← region material contexts world (if eraseFreeRegions && value == .static then .erased else value)
          pure (updated,TypeShape.reference pointee mutable value)
        | .rawPointer pointee mutable => do
          let (world,pointee) ← go fuel world contexts pointee
          pure (world,TypeShape.rawPointer pointee mutable)
        | .tuple references => do
          let mut world := world
          let mut ids := #[]
          for reference in references do
            let (updated,id) ← go fuel world contexts reference
            world := updated; ids := ids.push id
          pure (world,TypeShape.tuple ids)
        | .array element _ => do
          let .array _ length constructor := erasedNode.shape | throw "Invalid erased signature array shape"
          let (world,element) ← go fuel world contexts element
          pure (world,TypeShape.array element length constructor)
        | .dynamicObject value predicates => do
          let .dynamicTraitObject erasedPredicates _ _ := erasedNode.shape
            | throw "Invalid erased signature dynamic shape"
          unless predicates.size == erasedPredicates.size do throw "Invalid erased signature predicate count"
          let mut world := world
          let mut ids := #[]
          let mut principal := none
          for (predicate,erasedPredicate) in predicates.zip erasedPredicates do
            let some row := world.canonical.predicates[erasedPredicate]?
              | throw "Invalid erased signature predicate"
            let (arguments,term) ← match predicate with
              | .trait _ arguments bound =>
                unless bound.isEmpty do throw "Unsupported nested existential binder"
                pure (arguments,none)
              | .projection _ _ arguments term bound =>
                unless bound.isEmpty do throw "Unsupported nested existential binder"
                pure (arguments,some term)
              | .autoTrait _ bound =>
                unless bound.isEmpty do throw "Unsupported nested existential binder"
                pure (#[],none)
              | .unsupported tag => throw s!"Unsupported signature predicate {tag}"
            let mut args : Array MIR.GenericArg := #[]
            for argument in arguments do
              let .type reference := argument | throw "Unsupported signature predicate non-type argument"
              let (updated,id) ← go fuel world contexts reference
              world := updated; args := args.push (.Type id)
            let mut termId := none
            if let some term := term then
              let (updated,id) ← go fuel world contexts term
              world := updated; termId := some id
            let (updated,id) ← SourceCompilerWorld.internPredicate world {row with genericArgs := args, projectionTerm := termId}
            world := updated; ids := ids.push id
            if row.kind == .trait then principal := some id
          let (updated,value) ← region material contexts world (if eraseFreeRegions && value == .static then .erased else value)
          world := updated
          pure (world,TypeShape.dynamicTraitObject ids principal value)
        | _ => throw "Unsupported original signature constructor identity"
      SourceCompilerWorld.internType world shape layout "source signature type"
end Miri.Input.SourceSignatureTypes
