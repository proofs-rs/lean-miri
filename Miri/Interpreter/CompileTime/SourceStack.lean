import Miri.Interpreter.CompileTime.CallFrame
import Miri.Interpreter.CompileTime.FrameEntry
open Miri.Interpreter.CompileTime
namespace Miri.Interpreter.CompileTime.SourceStack
open CallFrame
structure Source where
  definition : Nat
  name : String
  required : Array Reference
  typeParameters : Nat := 0
  annotationDebug : Array String := #[]
  program : Program
  cleanup : Array Bool
  deriving Repr, DecidableEq
structure Frame where
  source : Source
  current : Option State := none
  typeArguments : Array Nat := #[]
  continuation : Option Call := none
  deriving Repr
structure Machine where
  frames : List Frame := []
  steps : Nat := 0
  counters : Nat := 0
  trace : Array (Nat × Nat × Nat × Bool) := #[]
  requiredRequests : Array (Nat × Nat × Reference) := #[]
  events : Array Counter.Event := #[]
  deriving Repr
inductive Outcome where
  | returned (value : Value) (machine : Machine)
  | failed (error : String) (machine : Machine)
  deriving Repr

def lookup (sources : Array Source) (definition : Nat) : Except String Source :=
  match sources.filter (·.definition == definition) with
  | #[source] => .ok source
  | _ => .error "missing or forged source definition"

def validateSource (source : Source) : Except String Unit := do
  unless source.cleanup.size == source.program.blocks.size do throw "cleanup metadata domain mismatch"
  unless source.program.argumentCount < source.program.locals.size && !source.program.blocks.isEmpty do
    throw "source frame local/block domain is absent"
  unless source.cleanup[0]? == some false do throw "source entry is a cleanup block"
  let target (index : Nat) : Except String Unit :=
    unless index < source.program.blocks.size do throw "source target block is absent"
  unless source.annotationDebug.isEmpty do throw "post-cleanup source retained a live annotation table"
  let rec ty : Nat → Ty → Except String Unit
    | 0,_ => throw "source type traversal exhausted"
    | _,.uint bits => unless bits == 32 do throw "calls source only covers u32"
    | _,.boolean | _,.unit | _,.never => pure ()
    | fuel+1,.pair a b => ty fuel a *> ty fuel b
  for shape in source.program.locals do ty 16384 shape
  let referenceType (value : Reference) : Ty :=
    match value with | .direct _ _ shape _ | .associated _ _ _ shape _ => shape
  let reference (value : Reference) : Except String Unit := do
    ty 16384 (referenceType value)
    unless referenceType value != .never do throw "uninhabited constant reference"
    -- CleanupPostBorrowck clears the annotation table but leaves operand indices.
    -- The index is retained metadata; it is never an executed table lookup.
    match value with
    | .direct _ _ _ _ => pure ()
    | .associated _ parameter _ _ _ => unless parameter < source.typeParameters do throw "source type parameter is absent"
  let placeType (value : Place) : Except String Ty := do
    let some initial := source.program.locals[value.slot]? | throw "source local is absent"
    let mut shape := initial
    for field in value.fields do
      match shape,field with
      | .pair a _,0 => shape := a
      | .pair _ b,1 => shape := b
      | _,_ => throw "source projection contradicts declared tuple type"
    pure shape
  let place (value : Place) : Except String Unit := do
    let _ ← placeType value
    pure ()
  let operandType (value : Operand) : Except String Ty :=
    match value with
    | .copy value | .move value => placeType value
    | .constant value => pure (referenceType value)
    | .sourceValue value => pure value.value.ty
  let operand (value : Operand) : Except String Unit := do
    match value with
    | .copy value | .move value =>
      unless (← placeType value) != .never do throw "source read of uninhabited local"
    | .constant value => reference value
    | .sourceValue value =>
      unless value.userType.isNone do throw "source user annotation unsupported"
      match value.value with
      | .uint bits number => unless bits == 32 && number < 2^32 do throw "invalid source scalar width/value"
      | .boolean _ | .unit => pure ()
      | _ => throw "unsupported raw source literal"
  let rvalueType (value : Rvalue) : Except String Ty := do
    match value with
    | .use value _ => operand value; operandType value
    | .binary kind left right =>
      operand left; operand right
      unless (← operandType left) == .uint 32 && (← operandType right) == .uint 32 do
        throw "source binary operands must be u32"
      pure (match kind with | .gt | .eq => .boolean | .div => .uint 32 | _ => .pair (.uint 32) .boolean)
  for value in source.required do reference value
  for block in source.program.blocks do
    for statement in block.statements do
      match statement with
      | .assign destination value =>
        place destination
        unless destination.fields.isEmpty do throw "projected source assignment unsupported"
        unless (← placeType destination) == (← rvalueType value) do throw "source assignment declared type mismatch"
      | .live slot | .dead slot =>
        unless slot > 0 && slot < source.program.locals.size do throw "invalid storage marker local"
      | .counter | .nop => pure ()
    match block.terminator with
    | .goto next => target next
    | .switch value cases otherwise =>
      operand value
      let shape ← operandType value
      unless shape == .uint 32 || shape == .boolean do throw "source switch type unsupported"
      let mut seen := #[]
      for (value,next) in cases do
        unless value < (if shape == .boolean then 2 else 2^32) && !seen.contains value do
          throw "invalid or duplicate source switch value"
        seen := seen.push value
        target next
      target otherwise
    | .assert value _ message next =>
      operand value
      unless (← operandType value) == .boolean do throw "assertion condition must be bool"
      match message with
      | .overflow _ left right => operand left *> operand right
      | .divisionByZero value => operand value
      target next
    | .call call =>
      -- operand.rs executes the FnDef const_ and span, not user_ty. Its raw
      -- annotation index survives PostCleanup as nonexecuted metadata.
      unless call.callSource == "normal" && call.functionSourceClass == .literalValue && call.abi == "rust" && !call.trackCaller do throw "unsupported FnDef call metadata"
      unless call.typeArguments.isEmpty do throw "generic source calls unsupported"
      unless call.argumentSpans.size == call.arguments.size do throw "call argument span domain mismatch"
      place call.destination
      unless call.destination.fields.isEmpty do throw "projected call destination unsupported"
      for value in call.arguments do operand value
      target call.target
      if let .cleanup unwind := call.unwind then
        target unwind
        unless source.cleanup[unwind]? == some true do throw "call unwind target is not a cleanup block"
    | .ret | .resume => pure ()

private def replaceTop (frame : Frame) (machine : Machine) : Machine :=
  {machine with frames := frame :: machine.frames.drop 1}

/-- Entry callbacks retain the execution World on failure. This interface does
not supply compiler normalization, allocation, or query admission. The source
namespace is explicitly local crate0; keys are physical definition indices. -/
def pushWithWorld (sources : Array Source)
    (resolve : Frame → Reference → FrameEntry.Action World String Unit)
    (definition : Nat) (arguments : Array Value) (types : Array Nat) (continuation : Option Call)
    (machine : Machine) (world : World) : Except String Unit × Machine × World := Id.run do
  let .ok source := lookup sources definition | return (.error "missing or forged source definition",machine,world)
  if let .error error := validateSource source then return (.error error,machine,world)
  unless source.typeParameters == types.size do return (.error "source generic arity mismatch",machine,world)
  -- Ordinary-call compatibility precedes raw pending push and its preamble.
  if continuation.isSome then
    unless source.program.argumentCount == arguments.size do return (.error "source call argument count mismatch",machine,world)
    for (argument,index) in arguments.zipIdx do
      unless source.program.locals[index+1]? == some argument.ty do
        return (.error "source call argument type mismatch",machine,world)
    let some caller := machine.frames.head? | return (.error "source call lacks caller",machine,world)
    let some call := continuation | return (.error "source call lacks continuation",machine,world)
    unless caller.source.program.locals[call.destination.slot]? == source.program.locals[0]? do
      return (.error "source call return destination type mismatch",machine,world)
  let frame : Frame := {source,current := none,typeArguments := types,continuation}
  let machine := {machine with frames := frame::machine.frames}
  let evaluate (pending : Frame) (reference : Reference) (state : Machine × World) :=
    let index := state.1.requiredRequests.size - machine.requiredRequests.size
    let machine := {state.1 with requiredRequests := state.1.requiredRequests.push (definition,index,reference)}
    let (result,world) := resolve pending reference state.2
    (result,(machine,world))
  let finish (pending : Frame) (state : Machine × World) :=
    match initializeState source.program arguments with
    | .error error => (.error error,state)
    | .ok initialized => (.ok {pending with current := some initialized},state)
  match FrameEntry.enter source.required evaluate finish frame (machine,world) with
  | .failed error _ _ state _ => return (.error error,state.1,state.2)
  | .ready ready state _ => return (.ok (),replaceTop ready state.1,state.2)

/-- Pure source comparisons only. Real compiler entry uses pushWithWorld;
this resolver never constructs a compiler query-success result. -/
def push (sources : Array Source) (resolve : Array Nat → Reference → Except String Value)
    (definition : Nat) (arguments : Array Value) (types : Array Nat) (continuation : Option Call)
    (machine : Machine) : Except String Unit × Machine :=
  let (result,machine,_) := pushWithWorld sources
    (fun frame reference world => ((resolve frame.typeArguments reference).map (fun _ => ()),world))
    definition arguments types continuation machine ()
  (result,machine)

private def record (definition : Nat) (current : State) (machine : Machine) : Machine :=
  let counter := match machine.frames.head? with
    | some frame => match frame.source.program.blocks[current.block]? with
      | some block => (block.statements[current.statement]? matches some .counter)
      | none => false
    | none => false
  {machine with trace := machine.trace.push (definition,current.block,current.statement,counter)}

private def commit (frame : Frame) (current : State) (machine : Machine) : Machine :=
  replaceTop {frame with current := some current} {machine with
    steps := current.steps,counters := current.counters,events := current.events}

/-- Closed scalar source execution only. There is no private allocation,
query-root ABI bypass, recursive interning or validation in this machine. -/
def runWithContext (sources : Array Source) (configuration : Machine → Counter.Config)
    (resolve : Array Nat → Reference → EStateM String World Value) : Nat → Machine → World → Outcome × World
  | 0,machine,world => (.failed "source stack traversal budget exhausted" machine,world)
  | fuel+1,machine,world => Id.run do
    let some frame := machine.frames.head? | return (.failed "source stack is empty" machine,world)
    let some saved := frame.current | return (.failed "pending source frame has no body PC" machine,world)
    let current := {saved with steps := machine.steps,counters := machine.counters,events := machine.events,trace := #[]}
    let machine := record frame.source.definition current machine
    if frame.source.cleanup[current.block]? == some true then
      return (.failed "unsupported CTFE cleanup block entered" machine,world)
    let (outcome,world) := stepWithWorld frame.source.program (configuration machine) (resolve frame.typeArguments) current world
    match outcome with
    | .failed error next => return (.failed error (commit frame next machine),world)
    | .running next => return runWithContext sources configuration resolve fuel (commit frame next machine) world
    | .calling call arguments next =>
      let machine := commit frame next machine
      let (result,machine,world) := pushWithWorld sources
        (fun frame reference world => match (resolve frame.typeArguments reference).run world with
          | .ok _ world => (.ok (),world)
          | .error error world => (.error error,world))
        call.callee arguments call.typeArguments (some call) machine world
      match result with
      | .error error => return (.failed error machine,world)
      | .ok () => return runWithContext sources configuration resolve fuel {machine with steps := machine.steps+1} world
    | .returned value next =>
      let machine := commit frame next machine
      match frame.continuation with
      | none => return (.returned value machine,world)
      | some call =>
        let machine := {machine with frames := machine.frames.drop 1}
        let some caller := machine.frames.head? | return (.failed "source return has no caller" machine,world)
        let some callerState := caller.current | return (.failed "source return caller is pending" machine,world)
        match write caller.source.program callerState call.destination value with
        | .error error => return (.failed error machine,world)
        | .ok written =>
          let caller := {caller with current := some {written with block := call.target,statement := 0}}
          return runWithContext sources configuration resolve fuel (replaceTop caller machine) world


/-- Uniform lint configuration for isolated comparisons. Production callers
can use runWithContext with root-first source-scope selection. -/
def runWithWorld (sources : Array Source) (config : Counter.Config)
    (resolve : Array Nat → Reference → EStateM String World Value)
    (fuel : Nat) (machine : Machine) (world : World) : Outcome × World :=
  runWithContext sources (fun _ => config) resolve fuel machine world

/-- Pure comparisons share the World-preserving machine; no query provider is supplied. -/
def run (sources : Array Source) (config : Counter.Config)
    (resolve : Array Nat → Reference → Except String Value) (fuel : Nat) (machine : Machine) : Outcome :=
  (runWithWorld sources config (fun types reference world =>
    match resolve types reference with
    | .ok value => .ok value world
    | .error error => .error error world) fuel machine ()).1

/-- Derive a constant's scalar frame result from another captured source frame.
This deliberately returns no compiler allocation or query-success constructor. -/
structure AssociatedSource where
  declaration : Nat
  selfType : Nat
  valueDefinition : Nat
  deriving Repr

/-- Syntactic source-impl matching for this restricted parameter-only fixture,
not a compiler-selected-instance table or a normalization answer. -/
def instantiate (rules : Array AssociatedSource) (types : Array Nat) : Reference → Except String Nat
  | .direct definition _ _ _ => .ok definition
  | .associated declaration parameter _ _ _ => do
    let some selfType := types[parameter]? | throw "missing source type parameter"
    match rules.filter (fun rule => rule.declaration == declaration && rule.selfType == selfType) with
    | #[rule] => pure rule.valueDefinition
    | _ => throw "missing or ambiguous associated source implementation"

def sourceConstant (sources : Array Source) (rules : Array AssociatedSource) (config : Counter.Config) :
    Nat → Array Nat → Reference → Except String Value
  | 0,_,_ => .error "source constant dependency budget exhausted"
  | fuel+1,types,reference => do
    let definition ← instantiate rules types reference
    let resolver := sourceConstant sources rules config fuel
    let (result,machine) := push sources resolver definition #[] #[] none {}
    match result with
    | .error error => .error error
    | .ok () => match run sources config resolver 1000000 machine with
      | .returned value _ => .ok value
      | .failed error _ => .error error
end Miri.Interpreter.CompileTime.SourceStack
