import Miri.Input.SourceConcreteTypes
import Miri.Input.Model.SourceAbi
import Miri.Input.SourceCompilerTypes
import Miri.Input.SourceTypeQueries
import Miri.Input.SourcePhysical
import Miri.Input.SourceSignatureTypes
import Miri.Input.SourceTraitSelection
import Miri.Input.SourceParamAttrs
import Miri.Input.SourceCompilerAutoTraits

/-! Demand-time Rust Item ABI from typed finite declarations. No JSON value,
MIR execution, compiler process, query catalog or private pool participates.
This initial common domain is scalar/unit/raw-pointer/array signatures and
source-backed Sized/Copy/MetaSized and safe Rust function-pointer callable
clauses/projections. Other forms fail at demand. -/
namespace Miri.Input.SourceAbi
open Miri.Interpreter
abbrev World := SourceCompilerWorld.World

private abbrev scalarConstant := SourceConcreteTypes.scalarConstant
private abbrev concreteType := SourceConcreteTypes.concreteType

private def builtin (physical : SourceTypes.Material) (target : ABI.RuntimeTargetDataLayout)
    (role : BuiltinTrait) (type : SourceTypes.Concrete) : Except String Bool := do
  if role != .copy then
    -- Sizedness belongs to the complete source-derived layout, not a list of
    -- primitive type names. Scalar backends are sized; memory carries the
    -- explicit DST flag. Never infer Sized from a zero byte-size alone.
    let layout ← SourcePhysical.calculate physical target type
    let some backend := layout.backendRepresentation | throw "typed ABI sizedness backend absent"
    let sized ← if backend.kind == .memory then
        match backend.sized with
        | some sized => pure sized
        | none => throw "typed ABI memory sizedness absent"
      else pure true
    if sized && layout.sizeBytes.isNone then throw "typed ABI sized layout byte size absent"
    if role == .sized then return sized
    if sized then return true -- every Sized type is MetaSized
    throw "typed ABI unsized MetaSized proof unsupported"
  go 1024 type
where
  go (fuel : Nat) (type : SourceTypes.Concrete) : Except String Bool := do
    let .succ fuel := fuel | throw "typed ABI builtin traversal exhausted"
    match type with
    | .primitive "bool" "" | .primitive "char" "" => pure true
    | .primitive kind name =>
      unless (kind == "int" && #["i8","i16","i32","i64","i128","isize"].contains name) ||
          (kind == "uint" && #["u8","u16","u32","u64","u128","usize"].contains name) do
        throw "typed ABI builtin primitive unsupported"
      pure true
    | .array element _ => go fuel element
    | .tuple fields => return (← fields.mapM (go fuel)).all id
    | .pointer tag _ =>
      unless tag == "raw_pointer_mut" || tag == "raw_pointer_const" do throw "typed ABI builtin reference unsupported"
      pure true
    | .functionPointer .. => pure true
    | _ => throw s!"typed ABI builtin {reprStr role} type unsupported"

/-- Generic finite unit-head selection. No trait name or language-item target
selects an implementation; unknown potentially overlapping heads reject. -/
def unitTraitImpl (material : Material) (definition : DefinitionId) : Except String DefinitionId := do
  let [declaration] := (material.traits.filter (·.definition == definition)).toList
    | throw "typed ABI ordinary trait source absent/ambiguous"
  unless declaration.complete && !declaration.isAuto && !declaration.isMarker && !declaration.isCoinductive &&
      declaration.isSafe && declaration.nonConst && declaration.parameterCount == 1 && declaration.hasSelf &&
      declaration.genericParent.isNone do throw "typed ABI ordinary trait declaration unsupported"
  for parent in declaration.superTraits do
    let [builtin] := (material.builtins.filter (fun b => b.role == .metaSized)).toList
      | throw "typed ABI MetaSized source declaration absent/ambiguous"
    unless builtin.pinnedCore && parent.definition == builtin.definition && parent.argumentCount == 1 && parent.selfParameter == some 0 &&
        parent.positive && parent.boundVariableCount == 0 do throw "typed ABI ordinary supertrait unsupported"
  let mut seen : Array DefinitionId := #[]
  let mut selected : Option DefinitionId := none
  for header in declaration.implementations do
    unless !seen.contains header.definition && header.traitDefinition == definition && header.argumentCount == 1 do
      throw "typed ABI impl header identity/trait mismatch"
    seen := seen.push header.definition
    let applies ← match header.selfHead with
      | .adt _ | .never => pure false
      | .tuple arity => pure (arity == 0)
      | .unsupported _ => throw "typed ABI impl head may overlap unit"
    if applies then
      unless header.parameterCount == 0 && header.genericParent.isNone && header.clauseCount == 0 &&
          header.clauseParent.isNone && header.positive && header.nonConst && header.final do
        throw "typed ABI conditional/negative/specializable unit impl unsupported"
      unless selected.isNone do throw "typed ABI unit impl ambiguous"
      selected := some header.definition
  let some implementation := selected | throw "typed ABI unit trait unsatisfied"
  return implementation

private def staticOutlives (type : SourceTypes.Concrete) : Except String Unit := go 1024 type
where
  go (fuel : Nat) (type : SourceTypes.Concrete) : Except String Unit := do
    let .succ fuel := fuel | throw "typed ABI outlives traversal exhausted"
    match type with
    | .primitive kind _ => unless #["bool","char","int","uint","float","str","never"].contains kind do throw "typed ABI outlives primitive unsupported"
    | .array element _ => go fuel element
    | .tuple fields => for field in fields do go fuel field
    | .pointer tag element =>
      unless #["raw_pointer_const","raw_pointer_mut","reference_static_const","reference_static_mut"].contains tag do
        throw "typed ABI erased reference cannot establish static outlives"
      go fuel element
    | .functionPointer inputs output .. =>
      for input in inputs do go fuel input
      go fuel output
    | _ => throw "typed ABI nominal/dyn outlives unsupported"

/-- Structural equality for the callable domain, not layout equivalence. -/
private def callableTypeEqual (a b : SourceTypes.Concrete) : Except String Bool := go 1024 a b
where
  go (fuel : Nat) (a b : SourceTypes.Concrete) : Except String Bool := do
    let .succ fuel := fuel | throw "typed ABI callable equality exhausted"
    match a,b with
    | .primitive ak an,.primitive bk bn => pure (ak == bk && an == bn)
    | .array a al,.array b bl => return al == bl && (← go fuel a b)
    | .pointer ak a,.pointer bk b => return ak == bk && (← go fuel a b)
    | .tuple a,.tuple b =>
      if a.size != b.size then return false
      for (a,b) in a.zip b do unless (← go fuel a b) do return false
      pure true
    | .functionPointer ai ao aSafety aa av,.functionPointer bi bo bs ba bv =>
      if aSafety != bs || aa != ba || av != bv || ai.size != bi.size then return false
      for (a,b) in ai.zip bi do unless (← go fuel a b) do return false
      go fuel ao bo
    | .nominal ..,_ | .dynamicObject ..,_ | .closure ..,_ | .patternNotNull ..,_ | .patternRange ..,_ |
      _,.nominal .. | _,.dynamicObject .. | _,.closure .. | _,.patternNotNull .. | _,.patternRange .. =>
      throw "typed ABI callable nominal/dyn/closure equality unsupported"
    | _,_ => pure false

/-- Pinned callable confirmation: function pointers tuple their inputs, while
closure RustCall signatures already contain their single tupled input. -/
private def callableOutput (physical : SourceTypes.Material) (target : ABI.RuntimeTargetDataLayout)
    (requested : CallableKind) (self args : SourceTypes.Concrete) : Except String SourceTypes.Concrete := do
  let .tuple _ := args | throw "typed ABI callable argument is not a tuple"
  let (inputs, output) ← match self with
    | .functionPointer inputs output safety convention variadic => do
      unless safety == .Safe && convention == .Rust && !variadic do
        throw "typed ABI callable requires safe nonvariadic Rust function pointer"
      pure (SourceTypes.Concrete.tuple inputs, output)
    | .closure _ arguments => do
      let some kind := arguments[arguments.size - 3]? | throw "typed ABI closure kind absent"
      let available ← match kind with
        | .primitive "int" "i8" => pure CallableKind.fn
        | .primitive "int" "i16" => pure CallableKind.fnMut
        | .primitive "int" "i32" => pure CallableKind.fnOnce
        | _ => throw "typed ABI closure kind unsupported"
      unless available == .fn || requested == .fnOnce || available == requested do
        throw "typed ABI closure callable kind obligation unsatisfied"
      let some (.functionPointer inputs output safety _ _) := arguments[arguments.size - 2]?
        | throw "typed ABI closure signature absent"
      unless safety == .Safe do
        throw "typed ABI callable closure signature is unsafe"
      let [input] := inputs.toList | throw "typed ABI closure signature tuple arity unsupported"
      let .tuple _ := input | throw "typed ABI closure signature input is not tupled"
      pure (input, output)
    | _ => throw "typed ABI callable self constructor unsupported"
  unless (← callableTypeEqual inputs args) do
    throw "typed ABI callable input tuple mismatch"
  unless (← builtin physical target .sized output) do throw "typed ABI callable output is not Sized"
  return output

/-- Reflexive early-region constraints add no rustc region constraint. A raw
late-bound goal requires binder instantiation first and is not discharged here. -/
def checkRegionOutlives (source : Input.SourceMaterial) (owner : DefinitionId)
    (longer shorter : SourceTypes.Region) : Except String Unit := do
  unless longer == shorter do throw "typed region outlives relation unsupported"
  match longer with
  | .static => pure ()
  | .earlyParameter index =>
    let parameters ← SourceDeclarations.fullParameters source.genericLayers owner
    unless parameters[index]? == some .region do throw "typed outlives early-region slot absent or wrong kind"
  | _ => throw "typed outlives requires retained early/static reflexivity; bound/erased relation unsupported"

private def checkClauses (source : Input.SourceMaterial) (abi : Material) (physical : SourceTypes.Material)
    (types : Array (Option SourceTypes.Concrete)) (constants : Array (Option Nat)) (target : ABI.RuntimeTargetDataLayout) (owner : DefinitionId) : Except String Unit :=
  go (source.genericLayers.size + 1) #[] owner
where
  go (fuel : Nat) (active : Array DefinitionId) (owner : DefinitionId) : Except String Unit := do
    let .succ fuel := fuel | throw "typed ABI generic clause traversal exhausted"
    unless !active.contains owner do throw "typed ABI generic clause owner cycle"
    let layers := source.genericLayers.filter (·.owner == owner)
    let [layer] := layers.toList | throw "typed ABI generic layer absent/ambiguous"
    let rows := abi.owners.filter (·.owner == owner)
    let [row] := rows.toList | throw "typed ABI constraint source absent/ambiguous"
    unless row.parent == layer.parent do throw "typed ABI clause/parameter parent mismatch"
    if let some parent := row.parent then go fuel (active.push owner) parent
    for clause in row.clauses do
      match clause with
      | .trait definition (some role) arguments =>
        let [self] := arguments.toList | throw "typed ABI builtin trait arguments unsupported"
        let declarations := abi.builtins.filter (·.role == role)
        let [declaration] := declarations.toList | throw "typed ABI builtin language declaration absent/ambiguous"
        unless declaration.definition == definition do throw "typed ABI builtin language identity mismatch"
        unless declaration.pinnedCore do throw "typed ABI builtin requires pinned core declaration source"
        let type ← SourceTypes.instantiate physical types constants self
        unless (← builtin physical target role type) do throw "typed ABI builtin obligation unsatisfied"
      | .trait definition none arguments =>
        if abi.callables.any (·.definition == definition) then
          let [declaration] := (abi.callables.filter (·.definition == definition)).toList
            | throw "typed ABI callable declaration ambiguous"
          let [self,args] := arguments.toList | throw "typed ABI callable trait arity unsupported"
          let _ ← callableOutput physical target declaration.kind (← SourceTypes.instantiate physical types constants self)
            (← SourceTypes.instantiate physical types constants args)
        else
          let [self] := arguments.toList | throw "typed ABI ordinary trait arguments unsupported"
          let self ← SourceTypes.instantiate physical types constants self
          if abi.traits.any (·.definition == definition) then
            let .tuple fields := self | throw "typed ABI ordinary unit impl self mismatch"
            unless fields.isEmpty do throw "typed ABI ordinary unit impl self mismatch"
            let _ ← unitTraitImpl abi definition
          else
            let some material := source.traitImpls | throw "typed ABI complete trait impl source unavailable"
            unless (← SourceTraitSelection.check physical abi material (builtin physical target) definition self) do
              throw "typed ABI ordinary trait obligation unsatisfied"
      | .projection definition parent arguments term =>
        let [declaration] := (abi.callables.filter fun row => row.definition == parent && row.output == some definition).toList
          | throw "typed ABI associated projection declaration unsupported"
        unless declaration.kind == .fnOnce do throw "typed ABI projection is not FnOnce Output"
        let [self,args] := arguments.toList | throw "typed ABI callable projection arity unsupported"
        let output ← callableOutput physical target declaration.kind (← SourceTypes.instantiate physical types constants self)
          (← SourceTypes.instantiate physical types constants args)
        unless (← callableTypeEqual output (← SourceTypes.instantiate physical types constants term)) do
          throw "typed ABI callable Output mismatch"
      | .regionOutlives longer shorter => checkRegionOutlives source owner longer shorter
      | .typeOutlives type region =>
        -- A concrete type with no non-static region outlives every retained
        -- early region. Unknown/erased references do not establish this.
        checkRegionOutlives source owner region region
        staticOutlives (← SourceTypes.instantiate physical types constants type)
      | .constHasType parameter type =>
        let some _ := constants[parameter]?.bind id | throw "typed ABI const clause argument absent"
        match ← SourceTypes.instantiate physical types constants type with
        | .primitive "uint" "usize" => pure ()
        | _ => throw "typed ABI const clause type unsupported"
      | _ => throw "typed ABI trait/projection/other obligation unsupported"

/-- Pinned callconv::layout_is_noundef over the shared canonical geometry. -/
private def layoutNoUndef (world : World) (id : Nat) : Except String Bool := go 1024 id
where
  go (fuel : Nat) (id : Nat) : Except String Bool := do
    let .succ fuel := fuel | throw "typed ABI initialization recursion exhausted"
    let some node := world.canonical.types[id]? | throw "typed ABI initialization type absent"
    let some layout := world.canonical.layouts[node.layoutId]? | throw "typed ABI initialization layout absent"
    let some backend := layout.backendRepresentation | throw "typed ABI initialization backend absent"
    match backend.kind with
    | .scalar =>
      let some scalar := backend.scalar | throw "typed ABI initialization scalar absent"
      return scalar.kind == .initialized
    | .scalarPair =>
      let some first := backend.first | throw "typed ABI initialization first scalar absent"
      let some second := backend.second | throw "typed ABI initialization second scalar absent"
      return first.kind == .initialized && second.kind == .initialized &&
        layout.sizeBytes == some (first.primitive.sizeBytes + second.primitive.sizeBytes)
    | .simdVector | .scalableSimdVector => return false
    | .memory =>
      let some fields := layout.fields | throw "typed ABI initialization fields absent"
      match fields.kind with
      | .primitive | .union => return false
      | .array =>
        if fields.fieldCount == 0 then return true
        let .array element .. := node.shape | throw "typed ABI initialization array element absent"
        go fuel element
      | .arbitrary =>
        let some variants := layout.variantsLayout | throw "typed ABI initialization variants absent"
        if variants.kind != .single then return false
        let children ← match node.shape with
          | .tuple fields => pure fields
          | .closure _ arguments _ => do
            let some (.Type tuple) := arguments.back? | throw "typed ABI initialization closure tuple absent"
            let some node := world.canonical.types[tuple]? | throw "typed ABI initialization closure captures absent"
            let .tuple fields := node.shape | throw "typed ABI initialization closure captures not tuple"
            pure fields
          | .adt data => do
            let some index := variants.variantIndex | throw "typed ABI initialization variant index absent"
            let some variant := data.variants.find? (·.index == index)
              | throw "typed ABI initialization variant fields absent"
            pure (variant.fields.map (·.typeId))
          | _ => throw "typed ABI initialization aggregate fields unsupported"
        let mut cursor := 0
        for index in fields.memoryOrder do
          let some child := children[index]? | throw "typed ABI initialization field type absent"
          let some node := world.canonical.types[child]? | throw "typed ABI initialization child absent"
          let some childLayout := world.canonical.layouts[node.layoutId]? | throw "typed ABI initialization child layout absent"
          let some bytes := childLayout.sizeBytes | throw "typed ABI initialization child unsized"
          if bytes != 0 then
            unless fields.offsetsBytes[index]? == some cursor do return false
            unless (← go fuel child) do return false
            cursor := cursor + bytes
        return layout.sizeBytes == some cursor

/-- Mirror the public FnAbi caller gate before consulting defining-crate
MIR. Unknown gates only permit results independent of whether deduction runs. -/
private def indirectBits (world : World) (optimizationDisabled : Bool) (callerIncremental : Option Bool)
    (definition : DefinitionId) (parameter typeId : Nat) : Except String Nat := do
  if optimizationDisabled || callerIncremental == some true then return 670
  let some source := world.canonical.sourceMaterial | throw "typed ABI indirect source unavailable"
  let some material := source.mirUses | throw s!"typed ABI indirect parameter {parameter} requires defining-crate MIR deduction evidence"
  let [declaration] := (material.declarations.filter (·.definition == definition)).toList
    | throw "typed ABI indirect MIR-use declaration absent/ambiguous"
  if let some compilation := declaration.compilation then
    if compilation.optimization == .no || compilation.incremental ||
        compilation.freezeLangItemPresent == some false then return 670
  if declaration.alwaysConst == some true then return 670
  -- Consumer-side absence of external MIR only means it was not encoded;
  -- deduced attributes may still have been encoded by the defining crate.
  let some body := declaration.body | do
    if definition.crateIndex == 0 then return 670
    throw s!"typed ABI indirect parameter {parameter} requires defining MIR availability evidence"
  if body.spreadArgument.isSome then return 670
  let usage ← SourceParamAttrs.parameterUsage body parameter
  if usage.mutated && usage.captured then return 670
  unless callerIncremental == some false do
    throw s!"typed ABI indirect parameter {parameter} requires caller incremental source"
  let some compilation := declaration.compilation
    | throw s!"typed ABI indirect parameter {parameter} requires defining-crate compilation options"
  unless compilation.freezeLangItemPresent == some true && declaration.alwaysConst == some false do
    throw s!"typed ABI indirect parameter {parameter} requires defining Freeze/comptime deduction prerequisites"
  if definition.crateIndex != 0 then
    throw s!"typed ABI indirect parameter {parameter} requires defining output-options evidence"
  -- These are the pinned DeducedParamAttrs::read_only/captures_none tests.
  -- NeedsDrop is only demanded when an actual root Drop use can affect a flag.
  let readOnly ← if usage.mutated then pure false else do
    if usage.dropped then throw "typed ABI deduced readonly requires source NeedsDrop evidence"
    if usage.sharedBorrowed then SourceCompilerAutoTraits.check world .freeze typeId
    else pure true
  let capturesNone ← if usage.captured then pure false else do
    if usage.dropped then throw "typed ABI deduced capture requires source NeedsDrop evidence"
    pure true
  let bits := if readOnly then 670 ||| 32 else 670
  return if capturesNone then bits ||| 7 else bits

private def passMode (world : World) (physical : SourceTypes.Material) (optimizationDisabled : Bool)
    (callerIncremental : Option Bool) (definition : DefinitionId) (parameter : Nat) (type : SourceTypes.Concrete) (id : Nat) : Except String AbiPassMode := do
  let some node := world.canonical.types[id]? | throw "typed ABI physical type absent"
  let some layout := world.canonical.layouts[node.layoutId]? | throw "typed ABI physical layout absent"
  let some bytes := layout.sizeBytes | throw "typed ABI unsized layout unsupported"
  if layout.backendRepresentation.bind (·.sized) == some false then
    throw "typed ABI unsized value pass mode unsupported"
  match type with
  | .dynamicObject .. | .patternNotNull .. | .patternRange .. => throw "typed ABI dyn/constrained type unsupported"
  | _ => pure ()
  let empty : AbiPassMode := ⟨.ignore,#[],none,none,none,none⟩
  if bytes == 0 then return empty
  let attrs (bits : Nat) (extension : ArgumentExtensionKind := .none) : AbiAttributes := ⟨bits,0,none,extension⟩
  let some backend := layout.backendRepresentation | throw "typed ABI backend unavailable"
  if backend.kind == .memory then
    if bytes ≤ 8 then
      let target ← SourcePhysical.target world
      -- CastTarget::size rounds the register aggregate to its ABI alignment.
      -- In particular i24 occupies four bytes, so a three-byte source must not
      -- forward NoUndef even when every source byte is initialized.
      let integerAlign := if bytes ≤ 1 then target.i8Align else if bytes ≤ 2 then target.i16Align
        else if bytes ≤ 4 then target.i32Align else target.i64Align
      let align := max (← integerAlign.bytes.mapError toString).toNat
        (← target.aggregateAlign.bytes.mapError toString).toNat
      let castSize := ((bytes + align - 1) / align) * align
      let initialized ← layoutNoUndef world id
      let register : AbiRegister := ⟨.integer,bytes*8,none⟩
      let cast : AbiCastTarget := ⟨#[],none,register,bytes,false,attrs (if initialized && castSize == bytes then 128 else 0)⟩
      return {empty with kind := .cast,castTarget := some cast,padI32Count := some 0}
    let bits ← indirectBits world optimizationDisabled callerIncremental definition parameter id
    let some align := layout.abiAlignBytes | throw "typed ABI indirect alignment unavailable"
    return {empty with kind := .indirect,attributes := #[⟨bits,bytes,some align,.none⟩],indirectMode := some .pointer}
  match type with
  | .primitive "bool" "" => return {empty with kind := .direct,attributes := #[attrs 128 .zeroExtend]}
  | .primitive "int" _ | .primitive "uint" _ | .primitive "char" "" =>
    return {empty with kind := .direct,attributes := #[attrs 128]}
  | .nominal .. =>
    let some backend := layout.backendRepresentation | throw "typed ABI nominal backend unavailable"
    let some scalar := backend.scalar | throw "typed ABI nominal scalar unavailable"
    unless backend.kind == .scalar && scalar.kind == .initialized && scalar.primitive.kind == .integer &&
        scalar.validRange.isSome do throw "typed ABI nominal noninteger scalar unsupported"
    let bool := scalar.primitive.sizeBytes == 1 && scalar.primitive.signed == some false && scalar.validRange == some (0,1)
    return {empty with kind := .direct,attributes := #[attrs 128 (if bool then .zeroExtend else .none)]}
  | .pointer tag pointee =>
    let some backend := layout.backendRepresentation | throw "typed ABI pointer backend unavailable"
    if tag == "raw_pointer_const" || tag == "raw_pointer_mut" then
      unless backend.kind == .scalar && backend.scalar.isSome do throw "typed ABI wide raw pointer unsupported"
      return {empty with kind := .direct,attributes := #[attrs 128]}
    unless #["reference_static_const","reference_static_mut","reference_erased_const","reference_erased_mut"].contains tag &&
        optimizationDisabled do throw "typed ABI reference requires source OptLevel::No"
    let .reference pointeeId _ _ := node.shape | throw "typed ABI reference canonical shape unavailable"
    let some pointeeNode := world.canonical.types[pointeeId]? | throw "typed ABI pointee type unavailable"
    let some pointeeLayout := world.canonical.layouts[pointeeNode.layoutId]? | throw "typed ABI pointee layout unavailable"
    let some align := pointeeLayout.abiAlignBytes | throw "typed ABI pointee alignment unavailable"
    -- Pinned layout.rs skips Freeze/Unpin at OptLevel::No. Both shared and
    -- mutable references then have size0 and no alias/read-only/writable flags;
    -- initialized pointer validity still supplies NoUndef|NonNull.
    let data : AbiAttributes := ⟨144,0,if align > 1 then some align else none,.none⟩
    if backend.kind == .scalar then
      return {empty with kind := .direct,attributes := #[data]}
    unless backend.kind == .scalarPair do throw "typed ABI reference backend unsupported"
    let metadata ← match pointee with
      | .primitive "str" "" => pure (attrs 128)
      | .dynamicObject _ => do
        -- The vtable scalar's source field type is &'static [usize; N]. Its
        -- pointee size is zero at optNo, and its alignment is usize alignment
        -- for every method count. No vtable identity or entry is invented.
        let row ← SourcePhysical.calculate physical (← SourcePhysical.target world) (.primitive "uint" "usize")
        let some align := row.abiAlignBytes | throw "typed ABI vtable pointee alignment unavailable"
        pure (AbiAttributes.mk 144 0 (if align > 1 then some align else none) .none)
      | _ => throw "typed ABI reference metadata unsupported"
    return {empty with kind := .pair,attributes := #[data,metadata]}
  | .functionPointer .. =>
    let some backend := layout.backendRepresentation | throw "typed ABI function pointer backend unavailable"
    unless backend.kind == .scalar && backend.scalar.isSome do throw "typed ABI function pointer scalar unavailable"
    return {empty with kind := .direct,attributes := #[attrs 144]}
  | _ => throw "typed ABI aggregate/nominal/dyn pass mode unsupported"

/-- Derive one ordinary Rust Item ABI without MIR capability. Source-table
indices and canonical pool handles are kept separate throughout. -/
def derive (initial : World) (callee : CallInstance) (extra : Array MIR.TyId) : Except String (World × FunctionAbi) := do
  unless extra.isEmpty do throw "typed source ABI variadic/extra arguments unsupported"
  let some source := initial.canonical.sourceMaterial | throw "typed ABI source universe unavailable"
  let some material := source.abi | throw "typed source ABI declarations unavailable"
  let some physical := source.physical | throw "typed source type expressions unavailable"
  let target := source.target
  unless target.architecture == "x86_64" && target.pointerSizeBits == 64 do throw "typed Rust ABI target unsupported"
  let key ← SourceCompilerWorld.keyOf initial callee
  let declarations := source.declarations.filter (·.definition == key.definition)
  let [declaration] := declarations.toList | throw "typed ABI Item declaration absent/ambiguous"
  let functions := material.functions.filter (·.definition == key.definition)
  let [function] := functions.toList | throw "typed ABI function signature absent/ambiguous"
  let parameters := declaration.parameters
  unless parameters.size == key.arguments.size do throw "typed ABI argument count mismatch"
  let mut world := initial
  let mut types := #[]
  let mut constants := #[]
  for (parameter,argument) in parameters.zip key.arguments do
    match parameter,argument with
    | .typeParameter,.Type id =>
      let type ← concreteType world target.pointerSizeBits id
      let (updated,actual) ← SourcePhysical.intern world type
      unless actual == id do throw "typed ABI argument canonical type identity mismatch"
      world := updated
      types := types.push (some type); constants := constants.push none
    | .constParameter,.Const id =>
      let (type,bits,bytes) ← scalarConstant world target.pointerSizeBits id
      let concrete ← concreteType world target.pointerSizeBits type
      let (updated,actual) ← SourcePhysical.intern world concrete
      unless actual == type do throw "typed ABI const type identity mismatch"
      let (updated,actual) ← SourceCompilerWorld.internScalarConstant updated type bits bytes
      unless actual == id do throw "typed ABI canonical const identity mismatch"
      world := updated
      types := types.push none; constants := constants.push (some bits)
    | .region,.Lifetime .Erased | .region,.Lifetime .Static =>
      types := types.push none; constants := constants.push none
    | _,_ => throw "typed ABI generic argument kind/region unsupported"
  -- Source parameter types remain obligations even if no body reads them.
  let mut owners : Array DefinitionId := #[]
  let mut owner := some key.definition
  while let some current := owner do
    unless !owners.contains current do throw "typed ABI owner cycle"
    owners := owners.push current
    let [layer] := (source.genericLayers.filter (·.owner == current)).toList | throw "typed ABI owner absent/ambiguous"
    for parameter in layer.parameters do
      if parameter.kind == .constParameter then
        let [declared] := (function.constParameterTypes.filter (·.definition == parameter.definition)).toList
          | throw "typed ABI const parameter type absent/ambiguous"
        match ← SourceTypes.instantiate physical types constants declared.type with
        | .primitive "uint" "usize" => pure ()
        | _ => throw "typed ABI declared const parameter type unsupported"
    owner := layer.parent
  checkClauses source material physical types constants (← SourcePhysical.target world) key.definition
  let signature := function.signature
  unless signature.abi == .Rust && !signature.cVariadic do
    throw "typed ABI convention/binder/variadic source unsupported"
  let (updated,_) ← SourceSignatureTypes.boundVariables world signature.boundVariables
  world := updated
  let attrs := function.attributes
  unless !attrs.trackCaller && !attrs.foreignItem && !attrs.dropGlue do throw "typed ABI function attribute adjustment unsupported"
  -- FnAbiDesc::for_instance normalizes the instantiated signature with
  -- erased regions. Preserve source identities until this codegen boundary.
  let output ← SourceTypes.instantiate physical types constants signature.output signature.boundVariables
    >>= SourceTypes.eraseRegions
  let (updated,result) ← SourcePhysical.intern world output
  world := updated
  let some resultNode := world.canonical.types[result]? | throw "typed ABI result type absent"
  let result : AbiArgument := ⟨result,resultNode.layoutId,← passMode world physical material.optimizationDisabled material.callerIncremental key.definition 0 output result⟩
  let mut inputs := #[]
  for (sourceType,index) in signature.inputs.zipIdx do
    let type ← SourceTypes.instantiate physical types constants sourceType signature.boundVariables
      >>= SourceTypes.eraseRegions
    let (updated,id) ← SourcePhysical.intern world type
    world := updated
    let some node := world.canonical.types[id]? | throw "typed ABI input type absent"
    inputs := inputs.push (AbiArgument.mk id node.layoutId (← passMode world physical material.optimizationDisabled material.callerIncremental key.definition (index+1) type id))
  let abi : FunctionAbi := {
    arguments := inputs,returnValue := result,callingConvention := ⟨.rust,none,none,none⟩,
    canUnwind := !attrs.neverUnwind && material.panicUnwinds,cVariadic := false,fixedCount := inputs.size }
  match world.canonical.compilerAbiLayoutSchema with
  | some "physical_ty_and_layout_v1" => pure ()
  | none =>
    unless world.canonical.functionAbis.isEmpty do throw "typed ABI existing format unavailable"
    world := {world with canonical := {world.canonical with compilerAbiLayoutSchema := some "physical_ty_and_layout_v1"}}
  | _ => throw "typed ABI physical format unsupported"
  return (world,abi)
end Miri.Input.SourceAbi
