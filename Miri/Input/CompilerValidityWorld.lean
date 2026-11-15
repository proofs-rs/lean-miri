import Miri.Input.SourceCompilerWorld
import Miri.Input.CompilerFactAdapters
import Miri.Input.CompilerPaths

/-! Validity queries over the current canonical source types. The structural
rules follow pinned rustc's opsem inhabitedness and trivial Freeze fast path.
Unknown trait/lang-item attributes are not negative boolean answers. -/
namespace Miri.Input.CompilerValidityWorld
open Miri.Interpreter
abbrev World := SourceCompilerWorld.World
private def node (world : World) (id : TypeId) : Except String TypeNode := do
  let some node := world.canonical.types[id]? | throw "validity canonical type absent"
  pure node
private def closureFields (world : World) (args : Array MIR.GenericArg) (count : Nat) : Except String (Array TypeId) := do
  let some (.Type tuple) := args.back? | throw "validity closure capture tuple absent"
  let .tuple fields := (← node world tuple).shape | throw "validity closure captures are not a tuple"
  unless fields.size == count do throw "validity closure capture count mismatch"
  pure fields

def classify (world : World) (id : TypeId) : Except String ValidityVisitor.TypeKind := do
  match (← node world id).shape with
  | .bool => pure .boolean | .char => pure .character | .int _ | .uint _ => pure .integer
  | .float _ => pure .float | .functionPointer .. => pure .functionPointer | .never => pure .never
  | .foreign _ => pure .foreign | .functionDefinition .. => pure .functionDefinition
  | .reference _ mutable _ => pure (.reference (mutable == .Mut))
  | .rawPointer pointee _ =>
    let rec sized (fuel : Nat) (id : TypeId) : Except String Bool := do
      let .succ fuel := fuel | throw "validity Sized traversal exhausted"
      match (← node world id).shape with
      | .str | .slice .. | .dynamicTraitObject .. | .foreign _ => pure false
      | .bool | .char | .int _ | .uint _ | .float _ | .never | .reference .. |
        .rawPointer .. | .functionDefinition .. | .functionPointer .. => pure true
      | .array child .. | .patternType child _ => sized fuel child
      | .tuple fields =>
        for child in fields do unless (← sized fuel child) do return false
        pure true
      | .closure _ arguments count =>
        for child in (← closureFields world arguments count) do unless (← sized fuel child) do return false
        pure true
      | _ => throw "validity raw-pointee Sized fact unsupported"
    pure (.rawPointer pointee (← sized (world.canonical.types.size+1) pointee))
  | .str => pure .string
  | .array element .. | .slice element => pure (.sequence element)
  | .dynamicTraitObject predicates .. => pure (.dynamic predicates)
  | .patternType base _ => pure (.pattern base)
  | .unsafeBinder .. => pure .unsafeBinder
  | .tuple _ | .closure .. => pure (.aggregate false false false)
  | _ => throw "validity classification needs unsupported nominal/alias attributes"

def metadataTail (world : World) (id : TypeId) : Except String ValidityVisitor.MetadataTail := go (world.canonical.types.size+1) id
where
  go (fuel : Nat) (id : TypeId) : Except String ValidityVisitor.MetadataTail := do
    let .succ fuel := fuel | throw "validity metadata tail recursion exhausted"
    match (← node world id).shape with
    | .dynamicTraitObject predicates .. => pure (.dynamic predicates)
    | .slice _ | .str => pure .sliceOrStr
    | .foreign _ => pure .foreign
    | .patternType base _ => go fuel base
    | .tuple fields =>
      let some tail := fields.back? | throw "validity metadata tail of empty tuple"
      go fuel tail
    | .adt data =>
      unless data.kind == .structKind do throw "validity metadata tail of enum/union"
      let [variant] := data.variants.toList | throw "validity struct variant absent"
      let some tail := variant.fields.back? | throw "validity metadata tail of empty struct"
      go fuel tail.typeId
    | _ => throw "validity metadata requested for a sized/unsupported tail"

def opsemInhabited (world : World) (id : TypeId) : Except String Bool := go (world.canonical.types.size+1) id
where
  go (fuel : Nat) (id : TypeId) : Except String Bool := do
    let .succ fuel := fuel | throw "validity inhabitedness recursion exhausted"
    match (← node world id).shape with
    | .bool | .char | .int _ | .uint _ | .float _ | .str | .foreign _ | .rawPointer .. |
      .functionPointer .. | .functionDefinition .. | .dynamicTraitObject .. | .slice _ => pure true
    | .never => pure false
    | .reference child .. | .patternType child _ => go fuel child
    | .tuple fields =>
      for child in fields do unless (← go fuel child) do return false
      pure true
    | .array child _ constructor =>
      unless constructor.canonicalValueConstructor do throw "validity array length source unavailable"
      if constructor.count == 0 then pure true else go fuel child
    | .closure _ arguments count =>
      for child in (← closureFields world arguments count) do unless (← go fuel child) do return false
      pure true
    | _ => throw "validity nominal/alias inhabitedness unsupported"

/-- A failed trivial fast path is unknown, not `Freeze = false`. -/
def isFreeze (world : World) (id : TypeId) : Except String Bool := go (world.canonical.types.size+1) id
where
  go (fuel : Nat) (id : TypeId) : Except String Bool := do
    let .succ fuel := fuel | throw "validity Freeze traversal exhausted"
    match (← node world id).shape with
    | .bool | .char | .int _ | .uint _ | .float _ | .str | .never | .reference .. |
      .rawPointer .. | .functionPointer .. | .functionDefinition .. => pure true
    | .array child .. | .slice child | .patternType child _ => go fuel child
    | .tuple fields =>
      for child in fields do let _ ← go fuel child
      pure true
    | _ => throw "validity Freeze requires unsupported trait evidence"

/-- Existing validity diagnostics use node labels, not `type_name::<T>()`. -/
def typeName (world : World) (id : TypeId) : Except String String := return (← node world id).display

/-- Pinned validity.rs only looks up capture bindings for local definitions.
External closure paths use the field number without a capture-name query. -/
def fieldPath (world : World) (layout : Miri.ABI.TyAndLayout TypeId) (index : Nat) (child : TypeId) :
    Except String Miri.Memory.PathElem := do
  match (← node world layout.ty).shape with
  | .closure definition .. =>
    let some raw := world.canonical.definitions[definition]? | throw "validity closure definition absent"
    let frames := world.canonical.queries.frameMetadata
    unless frames.crates.any (·.1 == frames.localCrate) do throw "validity source crate locality unavailable"
    unless raw.crateIndex != frames.localCrate do throw "validity local capture-name evidence unavailable"
    pure (.capturedVar (toString index))
  | .tuple _ => pure (.tupleElem index)
  | .array .. | .slice _ => pure (.arrayElem index)
  | .dynamicTraitObject .. =>
    unless index == 0 do throw "validity dynamic field index is not zero"
    pure (.dynDowncast (← typeName world child))
  | .adt data =>
    if let .Multiple _ _ tagField _ := layout.layout.variants then
      if tagField == index && data.kind == .enumKind then return .enumTag
    let .Single variant := layout.layout.variants | throw "validity ADT field before variant selection"
    let some variant := data.variants.find? (·.index == variant) | throw "validity ADT variant absent"
    let some field := variant.fields.find? (·.index == index) | throw "validity ADT field absent"
    pure (.field field.name)
  | _ => throw "validity aggregate diagnostic field unsupported"

private def query (prepared : CompilerFactAdapters.Prepared) (access : SourceCompilerWorld.Access S)
    (source : World → Except String A) (legacy : Unit → Except String A) : EStateM StepError S A := do
  let result ← match access.get (← get) with
    | some world => pure (if world.canonical.sourceMaterial.isSome then source world else legacy ())
    | none =>
      if prepared.context.runtime.source.sourceMaterial.isSome then
        throw (.unsupported "validity source compiler World unavailable")
      pure (legacy ())
  match result with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"compiler validity query: {error}")

def hooks (prepared : CompilerFactAdapters.Prepared) (access : SourceCompilerWorld.Access S)
    (base : ValidityVisitor.Hooks P S C E Fn Abi Pad) : ValidityVisitor.Hooks P S C E Fn Abi Pad :=
  {base with
    classify := fun _ id => query prepared access (classify · id) (fun _ => CompilerFactAdapters.validityKind prepared id)
    metadataTail := fun _ id => query prepared access (metadataTail · id) (fun _ => CompilerFactAdapters.metadataTail prepared id)
    typeName := fun _ id => query prepared access (typeName · id) (fun _ => ((prepared.context.runtime.node id).mapError toString).map (·.display))
    opsemInhabited := fun _ id => query prepared access (opsemInhabited · id) (fun _ => CompilerFacts.boolean prepared.context id "opsem_inhabited")
    isFreeze := fun _ id => query prepared access (isFreeze · id) (fun _ => CompilerFacts.boolean prepared.context id "is_freeze")
    fieldPath := fun _ layout index child => query prepared access (fieldPath · layout index child)
      (fun _ => CompilerPaths.fieldPath prepared.context layout index child)}
/-- An actual empty tuple row determines unit validity queries in source mode.
The statement uses canonical row/shape evidence, not a layout-based type guess
or a premise asserting success of a machine callback. -/
theorem hooks_unit_at (prepared : CompilerFactAdapters.Prepared)
    (access : SourceCompilerWorld.Access S)
    (base : ValidityVisitor.Hooks P S C E Fn Abi Pad) (choice : C)
    (before : S) (world : World) (id : TypeId) (value : TypeNode)
    (present : access.get before = some world)
    (source : world.canonical.sourceMaterial.isSome = true)
    (row : world.canonical.types[id]? = some value)
    (shape : value.shape = .tuple #[]) :
    (hooks prepared access base).classify choice id before =
      .ok (.aggregate false false false) before ∧
    (hooks prepared access base).typeName choice id before = .ok value.display before ∧
    (hooks prepared access base).opsemInhabited choice id before = .ok true before := by
  constructor
  · simp [hooks, query, classify, node, present, source, row, shape,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
      pure, EStateM.pure, Except.bind, Except.pure] <;> rfl
  constructor
  · simp [hooks, query, typeName, node, present, source, row,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
      pure, EStateM.pure, Except.bind, Except.pure] <;> rfl
  · simp [hooks, query, opsemInhabited, opsemInhabited.go, node, present, source, row, shape,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
      pure, EStateM.pure, Except.bind, Except.pure] <;> rfl

/-- Legacy compiler facts are used only under the actual World/runtime guard.
The hypotheses identify pure compiler data; no machine callback is assumed
successful, and a missing source World is not silently treated as legacy. -/
theorem hooks_legacy_at (prepared : CompilerFactAdapters.Prepared)
    (access : SourceCompilerWorld.Access S)
    (base : ValidityVisitor.Hooks P S C E Fn Abi Pad) (choice : C)
    (before : S) (id : TypeId) (value : TypeNode)
    (kindValue : ValidityVisitor.TypeKind) (inhabitedValue : Bool)
    (mode : match access.get before with
      | some world => world.canonical.sourceMaterial.isSome = false
      | none => prepared.context.runtime.source.sourceMaterial.isSome = false)
    (kind : CompilerFactAdapters.validityKind prepared id = .ok kindValue)
    (name : prepared.context.runtime.node id = .ok value)
    (inhabited : CompilerFacts.boolean prepared.context id "opsem_inhabited" = .ok inhabitedValue) :
    (hooks prepared access base).classify choice id before = .ok kindValue before ∧
    (hooks prepared access base).typeName choice id before = .ok value.display before ∧
    (hooks prepared access base).opsemInhabited choice id before = .ok inhabitedValue before := by
  cases present : access.get before <;> simp only [present] at mode
  all_goals
    constructor
    · simp [hooks, query, present, mode, kind, get, getThe, MonadStateOf.get,
        EStateM.get, bind, EStateM.bind, pure, EStateM.pure] <;> rfl
    constructor
    · simp [hooks, query, present, mode, name, Except.map, Except.mapError,
        get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure] <;> rfl
    · simp [hooks, query, present, mode, inhabited, get, getThe, MonadStateOf.get,
        EStateM.get, bind, EStateM.bind, pure, EStateM.pure] <;> rfl

end Miri.Input.CompilerValidityWorld
