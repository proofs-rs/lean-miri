import Miri.Input.SourceMirPlaces

/-! Generic typed source rvalues and projection facts. This constructs fixed MIR
syntax only. Unsize/vtable/instance operations remain actual interpreter demands;
no method winner, function allocation or vtable identity is selected here. -/
namespace Miri.Input.SourceMirRvalues
structure Context where
  world : SourceCompilerWorld.World
  localTypes : Array Nat
  types : Array (Option Nat)
  definitions : Array (Option Nat)
  constant : SourceMir.Constant → Except String MIR.ConstOperand

def known (value : SourceMir.Operator α) : Except String α :=
  match value with | .known value => pure value | .unsupported tag => throw s!"Unsupported source MIR operator {tag}"
def place (c : Context) (p : SourceMir.Place) : Except String (MIR.Place × PlaceFact) :=
  SourceMirPlaces.lower c.world c.localTypes c.types p
private def shape (c : Context) (id : Nat) : Except String TypeShape := do
  let some node := c.world.canonical.types[id]? | throw "Invalid source rvalue type handle"
  return node.shape

def operand (c : Context) (op : SourceMir.Operand) : Except String (MIR.Operand × Nat × Array PlaceFact) := do
  match op with
  | .copy p =>
    let (p,fact) ← place c p
    return (.Copy p,fact.typeId,#[fact])
  | .move p =>
    let (p,fact) ← place c p
    return (.Move p,fact.typeId,#[fact])
  | .constant value =>
    let value ← c.constant value
    return (.Constant value,value.value.typeId,#[])
  | .runtimeChecks check reference =>
    let some type := c.types[reference]?.join | throw "source runtime-check bool type unavailable"
    return (.RuntimeChecks check,type,#[])
  | .unsupported tag => throw s!"Unsupported source MIR operand {tag}"
/-- Assertion messages retain operand identities and are interpreted by the
fixed Assert implementation; lowering does not evaluate failure operands. -/
def assertion (c : Context) (message : SourceMir.AssertKind) : Except String (MIR.AssertKind × Array PlaceFact) := do
  match message with
  | .boundsCheck length index =>
    let (length,_,a) ← operand c length
    let (index,_,b) ← operand c index
    return (.BoundsCheck length index,a ++ b)
  | .overflow operator left right =>
    let (left,_,a) ← operand c left
    let (right,_,b) ← operand c right
    return (.Overflow (← known operator) left right,a ++ b)
  | .overflowNeg value =>
    let (value,_,facts) ← operand c value
    return (.OverflowNeg value,facts)
  | .divisionByZero value =>
    let (value,_,facts) ← operand c value
    return (.DivisionByZero value,facts)
  | .remainderByZero value =>
    let (value,_,facts) ← operand c value
    return (.RemainderByZero value,facts)
  | .invalidEnumConstruction value =>
    let (value,_,facts) ← operand c value
    return (.InvalidEnumConstruction value,facts)
  | .resumedAfterReturn kind => return (.ResumedAfterReturn (← known kind),#[])
  | .resumedAfterPanic kind => return (.ResumedAfterPanic (← known kind),#[])
  | .resumedAfterDrop kind => return (.ResumedAfterDrop (← known kind),#[])
  | .misalignedPointerDereference required found =>
    let (required,_,a) ← operand c required
    let (found,_,b) ← operand c found
    return (.MisalignedPointerDereference required found,a ++ b)
  | .nullPointerDereference => return (.NullPointerDereference,#[])
  | .nullReferenceConstructed => return (.NullReferenceConstructed,#[])
  | .unsupported tag => throw s!"Unsupported source MIR assertion {tag}"
private def operands (c : Context) (values : Array SourceMir.Operand) :
    Except String (Array MIR.Operand × Array Nat × Array PlaceFact) := do
  let mut result := #[]
  let mut types := #[]
  let mut facts := #[]
  for value in values do
    let (value,type,extra) ← operand c value
    result := result.push value; types := types.push type; facts := facts ++ extra
  return (result,types,facts)
private def arguments (c : Context) (values : Array SourceTypes.Argument) : Except String (Array MIR.GenericArg) :=
  values.mapM fun value => do
    let .type ref := value | throw "Unsupported source aggregate non-type argument"
    let some id := c.types[ref]?.join | throw "Invalid source aggregate argument not prepared"
    return .Type id

/-- The expected destination comes from the independently derived place path.
Aggregate/reference/unsize constructors check their source type annotations at
this boundary; runtime compiler leaves remain unresolved until demanded. -/
def lower (c : Context) (expected : Nat) (value : SourceMir.Rvalue) : Except String (MIR.Rvalue × Array PlaceFact) := do
  match value with
  | .use value retag =>
    let (value,type,facts) ← operand c value
    unless type == expected do throw "Invalid source Use/destination type mismatch"
    return (.Use value (if retag then .Yes else .No),facts)
  | .binary operator a b =>
    let (a,_,af) ← operand c a
    let (b,_,bf) ← operand c b
    return (.BinaryOp (← known operator) a b,af ++ bf)
  | .unary operator value =>
    let (value,_,facts) ← operand c value
    return (.UnaryOp (← known operator) value,facts)
  | .reference region borrow p =>
    let (p,fact) ← place c p
    let borrow ← known borrow
    let mutable ← match borrow with
      | .Shared => pure MIR.Mutability.Not
      | .Mut _ => pure .Mut
      | .Fake _ => throw "Unsupported source fake borrow recipe"
    match region with
    | .erased | .static => pure ()
    | _ => throw "Unsupported source reference region binder"
    let .reference pointee actual .Erased ← shape c expected | throw "Invalid source reference destination type"
    unless actual == mutable do throw "Invalid source reference mutability mismatch"
    unless pointee == fact.typeId do throw "Invalid source reference pointee type mismatch"
    -- Instance::instantiate_mir_and_normalize_erasing_regions erases the
    -- region, including a source static region, in the executable instance.
    return (.Ref .Erased borrow p,#[fact])
  | .rawPointer kind p =>
    let (p,fact) ← place c p
    let kind ← known kind
    let expectedMutability := match kind with
      | .Const => MIR.Mutability.Not
      | .Mut | .FakeForPtrMetadata => .Mut
    let .rawPointer pointee actual ← shape c expected | throw "Invalid source raw-pointer destination type"
    unless pointee == fact.typeId && actual == expectedMutability do
      throw "Invalid source raw-pointer pointee/mutability mismatch"
    return (.RawPtr kind p,#[fact])
  | .aggregateTuple values =>
    let (values,types,facts) ← operands c values
    let .tuple fields ← shape c expected | throw "Invalid source tuple destination type"
    unless fields == types do throw "Invalid source tuple field types"
    return (.Aggregate .Tuple values,facts)
  | .aggregateArray element values =>
    let some element := c.types[element]?.join | throw "Invalid source array element type not prepared"
    let (values,types,facts) ← operands c values
    let .array actual _ count ← shape c expected | throw "Invalid source array aggregate destination type"
    unless actual == element && count.count == values.size && types.all (· == element) do
      throw "Invalid source array aggregate element type/count"
    return (.Aggregate (.Array element) values,facts)
  | .aggregateClosure definition args values =>
    let some definition := c.definitions[definition]?.join | throw "Invalid source closure definition not prepared"
    let args ← arguments c args
    let (values,types,facts) ← operands c values
    let .closure actual actualArgs count ← shape c expected | throw "Invalid source closure aggregate destination type"
    unless actual == definition && actualArgs == args && count == values.size do
      throw "Invalid source closure aggregate identity/arguments/capture count"
    let some (.Type tupled) := args.back? | throw "Invalid source closure tupled upvars argument"
    let .tuple captures ← shape c tupled | throw "Invalid source closure tupled upvars type"
    unless captures == types do throw "Invalid source closure capture types"
    return (.Aggregate (.Closure definition args) values,facts)
  | .aggregateAdt definition variant args userType activeField values =>
    let some definition := c.definitions[definition]?.join | throw "Invalid source ADT definition not prepared"
    let args ← arguments c args
    let (values,types,facts) ← operands c values
    let .adt actual ← shape c expected | throw "Invalid source ADT aggregate destination type"
    unless actual.definition == definition && actual.args == args do
      throw "Invalid source ADT aggregate identity/arguments"
    let some selected := actual.variants.find? (·.index == variant)
      | throw "Invalid source ADT aggregate variant"
    match activeField with
    | some field =>
      let some selected := selected.fields.find? (·.index == field)
        | throw "Invalid source union aggregate field"
      unless types == #[selected.typeId] do throw "Invalid source union aggregate operand type"
    | none =>
      unless selected.fields.map (·.typeId) == types do
        throw "Invalid source ADT aggregate field types"
    return (.Aggregate (.Adt definition variant args userType activeField) values,facts)
  | .pointerCoercion coercion value target source =>
    let (value,sourceType,facts) ← operand c value
    let some target := c.types[target]?.join | throw "Invalid source coercion target not prepared"
    unless target == expected do throw "Invalid source coercion target/destination type mismatch"
    let coercion ← known coercion
    match coercion with
    | .Unsize =>
      match ← shape c sourceType,← shape c target with
      | .reference _ sourceMut _,.reference _ targetMut _
      | .rawPointer _ sourceMut,.rawPointer _ targetMut =>
        unless sourceMut == targetMut do throw "Unsupported source unsize mutability adjustment"
      | _,_ => throw "Unsupported source unsize pointer forms"
    | .ReifyFnPointer safety =>
      let .functionDefinition _ _ signature bound ← shape c sourceType
        | throw "Invalid source reification operand is not a function definition"
      let .functionPointer pointer pointerBound ← shape c target
        | throw "Invalid source reification target is not a function pointer"
      unless bound.isEmpty && pointerBound.isEmpty do
        throw "Unsupported source reification higher-ranked signature"
      unless pointer.safety == safety && (signature.safety == .Safe || safety == .Unsafe) do
        throw "Invalid source reification safety adjustment"
      unless signature.inputs == pointer.inputs && signature.output == pointer.output &&
          signature.abi == pointer.abi && signature.cVariadic == pointer.cVariadic do
        throw "Unsupported source reification signature normalization"
    | _ => throw "Unsupported source pointer coercion"
    return (.Cast (.PointerCoercion coercion (← known source)) value target,facts)
  | .cast kind value target =>
    let (value,_,facts) ← operand c value
    let some target := c.types[target]?.join | throw "Invalid source cast target not prepared"
    unless target == expected do throw "Invalid source cast target/destination type mismatch"
    return (.Cast (← known kind) value target,facts)
  | .discriminant p =>
    let (p,fact) ← place c p
    return (.Discriminant p,#[fact])
  | _ => throw "Unsupported typed source MIR rvalue"
end Miri.Input.SourceMirRvalues
